#include "Checker/PSA/Vulnerability.h"
#include "Checker/PSA/VulnerabilityRegistry.h"
#include "DyckAA/DyckAliasAnalysis.h"
#include "IR/SEG/SEGArgumentNode.h"
#include "IR/SEG/SEGCallSite.h"
#include "IR/SEG/SEGSimpleSite.h"
#include "IR/SEG/SEGValue.h"
#include "Utils/Mock/LibMeta.h"

#include <regex>
#include <string>
#include <iostream>
#include <cstdlib>
#include <cxxabi.h>
#include <stdio.h>
#include <dlfcn.h>

static cl::list<std::string>
    OCCGQueryFunc("occg-query-func", cl::OneOrMore);
static cl::opt<string>
    LibSwiftDemangle("lib-swift-demangle", cl::Optional);


using namespace llvm;

#define DEBUG_TYPE "OCCallGraph"

struct OCCallGraphPass : public ModulePass
{
  static char ID;
  OCCallGraphPass() : ModulePass(ID) {}

  class OCCallGraph
  {
  public:
    StringMap<std::set<std::string>> Parents;
    StringMap<std::set<std::string>> Children;
  };

  void getAnalysisUsage(AnalysisUsage &AU) const override
  {
    // This is to satisfy Condition 2.
    AU.addRequired<DyckAliasAnalysis>();
    AU.setPreservesAll();
  }

  bool runOnModule(Module &M) override
  {
    DyckAliasAnalysis *canary = &getAnalysis<DyckAliasAnalysis>();
    OCCallGraph OCG;
    std::unordered_map<CallInst *, std::string> ValClassNameMap;
    std::unordered_map<CallInst *, std::string> ValFuncNameMap;

    auto libm_hundle = getLibmHandle(LibSwiftDemangle.getValue().c_str());
    for (Function &F : M)
    {
      for (BasicBlock &B : F)
      {
        for (Instruction &I : B)
        {
          if (auto *CI = dyn_cast<CallInst>(&I))
          {
            if (auto *Callee = CI->getCalledFunction())
            {
              if (Callee->getName().count("_objc_") <= 0)
              {
                if (Callee->getName().startswith("_$")){
                  // parsing the swift call
                  auto FuncName = Callee->getName().str();
                  auto demangleStr = getSwiftDemangledName(libm_hundle, FuncName);
                  if (demangleStr == ""){
                    continue;
                  }
                  auto demangledInfo = parseDemangledStr(demangleStr);
                  ValFuncNameMap[CI] = demangledInfo.functionName;
                  ValClassNameMap[CI] = demangledInfo.className;
                }
                continue;
              }
              // Check first arg(class)
              
              if (auto *LI = dyn_cast<LoadInst>(CI->getArgOperand(0)))
              {
                auto classname = getClassNameFromLoad(CI, LI);
                if (classname != ""){
                  ValClassNameMap[CI] = classname;
                }
              }
              else if (auto *ChainedCI = dyn_cast<CallInst>(CI->getArgOperand(0)))
              {
                if (auto ChainedCI_fun = ChainedCI->getCalledFunction()->getName().count("plankton_undefined") > 0){
                    ValClassNameMap[CI] = "NSObject";
                }
                else
                {
                  auto *ChainedCIFirstInst = dyn_cast<CallInst>(ChainedCI->getArgOperand(0));
                  if (ValClassNameMap.count(ChainedCI) > 0)
                  {
                    ValClassNameMap[CI] = ValClassNameMap[ChainedCI];
                  }
                  else if (ChainedCI->getName().count("_objc_alloc") > 0)
                  {
                    assert(isa<LoadInst>(ChainedCI->getArgOperand(0)));
                    if (auto *LI =dyn_cast<LoadInst>(ChainedCI->getArgOperand(0)))
                    { 
                      auto classname = getClassNameFromLoad(CI, LI);
                      if (classname != ""){
                        ValClassNameMap[CI] = classname;
                      }
                    }
                  }
                }
              }
              else if (auto *ChainedITPI = dyn_cast<IntToPtrInst>(CI->getArgOperand(0))){
                auto aliasSet = canary->getAliasSet(ChainedITPI);
                for(auto aliasIt=aliasSet->begin();aliasIt!=aliasSet->end();aliasIt++){
                    errs()<<"alias: "<<**aliasIt<<"\n";
                }
                auto *ChainedCIFirstOp = ChainedITPI->getOperand(0);
                if (auto *LI = dyn_cast<LoadInst>(ChainedCIFirstOp)){
                  auto classname = getClassNameFromLoad(CI, LI);
                  if (classname != ""){
                    ValClassNameMap[CI] = classname;
                  }
                }
                else if (auto *ChainedCI = dyn_cast<CallInst>(ChainedCIFirstOp)){
                  if (auto ChainedCI_Fun = ChainedCI->getCalledFunction()){
                    if (ChainedCI_Fun->getName().count("plankton_undefined") > 0)
                    {
                      ValClassNameMap[CI] = "NSObject";
                    }
                    else
                    {
                      auto *ChainedCIFirstInst = dyn_cast<CallInst>(ChainedCI->getArgOperand(0));
                      if (ValClassNameMap.count(ChainedCIFirstInst) > 0)
                      {
                        ValClassNameMap[CI] = ValClassNameMap[ChainedCIFirstInst];
                      }
                      else if (ChainedCI_Fun->getName().count("_objc_alloc") > 0)
                      {
                        // assert(isa<LoadInst>(ChainedCI->getArgOperand(0)));
                        if (auto *PI = dyn_cast<PtrToIntInst>(ChainedCI->getArgOperand(0))){
                          auto *PIFirstOp = PI->getOperand(0);
                          if (auto *LI = dyn_cast<LoadInst>(PIFirstOp))
                          {
                            auto classname = getClassNameFromLoad(CI, LI);
                            if (classname != ""){
                              ValClassNameMap[CI] = classname;
                            }
                          }
                        }
                        if (auto *LI = dyn_cast<LoadInst>(ChainedCI->getArgOperand(0)))
                        {
                          auto classname = getClassNameFromLoad(CI, LI);
                          if (classname != ""){
                            ValClassNameMap[CI] = classname;
                          }
                        }
                      }
                    }
                  }
                }
                else if (!isa<Instruction>(ChainedCIFirstOp)){
                  llvm::StringRef FunctionName = CI->getParent()->getParent()->getName();
                  if (FunctionName.startswith("-")){
                    std::size_t StartPos = FunctionName.str().find("[") + 1;
                    std::size_t EndPos = FunctionName.str().find(" ", StartPos);
                    std::size_t ClassNameLength = EndPos - StartPos;
                    std::string classname = FunctionName.str().substr(StartPos, ClassNameLength);
                    ValClassNameMap[CI] = classname;
                  }
                }
              }         
              else if (auto *ChainedBCI = dyn_cast<BitCastInst>(CI->getArgOperand(0))){
                auto *ChainedBCIOp = ChainedBCI->getOperand(0);
                auto ChainedType = ChainedBCIOp->getType();
                if (ChainedType->isPointerTy()) {
                    Type* ChainedPEType = ChainedType->getPointerElementType();
                    if (ChainedPEType->isStructTy()) {
                      StructType* structType = cast<StructType>(ChainedPEType);
                      auto structName = structType->getName().str();
                      size_t pos = structName.find('.');
                      if (pos != std::string::npos) {
                          structName = structName.substr(pos + 1);
                      }
                      ValClassNameMap[CI] = structName;
                    }
                }
              }

              // Check second arg(function)
              if (Callee->getName().count("_objc_msgSend") <= 0)
              {
                continue;
              }
              if (Callee->getName().count("_objc_msgSend$") > 0){
                std::string FuncName = "unknown";
                FuncName = Callee->getName().substr(Callee->getName().str().find("$")+1);
                ValFuncNameMap[CI] = FuncName;
              }
              if (auto *Int2PtrVal =
                      dyn_cast<ConstantExpr>(CI->getArgOperand(1)))
              {
                Constant *GVal = Int2PtrVal->getOperand(0);
                assert(GVal);
                assert(isa<GlobalVariable>(GVal));
                if (auto *GV = dyn_cast<GlobalVariable>(GVal))
                {
                  if (!GV->hasInitializer())
                  {
                    continue;
                  }
                  std::string FuncName = "unknown";
                  Constant *GI = GV->getInitializer();
                  if (auto *CA = dyn_cast<ConstantDataArray>(GI))
                  {
                    FuncName = CA->getAsString();
                  }
                  else if (auto *CS = dyn_cast<ConstantDataSequential>(GI))
                  {
                    FuncName = CS->getAsString();
                  }
                  else if (auto *CV = dyn_cast<ConstantDataVector>(GI))
                  {
                    FuncName = CV->getAsString();
                  }
                  ValFuncNameMap[CI] = FuncName;
                }
              }
            }
          }
        }
      }
    }

    DEBUG(
    outs() << ValClassNameMap.size() << "\n";
    outs() << ValFuncNameMap.size() << "\n";
    );

    for (auto &It : ValFuncNameMap)
    {
      auto FuncName = It.second;
      std::string ParentName = It.first->getParent()->getParent()->getName().str();
      ParentName = parseOCFunName(ParentName);
      // llvm::StringRef a(ParentName.str());
      auto demangleStr = getSwiftDemangledName(libm_hundle, ParentName);
      if (demangleStr != ""){
        auto demangledInfo = parseDemangledStr(demangleStr);
        ParentName = demangledInfo.functionName;
        if (demangledInfo.className != ""){
          if (demangledInfo.mode == "@objc"){
            ParentName = demangledInfo.mode + " " + demangledInfo.className + " " + demangledInfo.functionName;
          }
          else{
            ParentName = demangledInfo.className + " " + demangledInfo.functionName;
          }
        }
      }

      std::string FullName;
      if (ValClassNameMap.count(It.first) > 0)
      {
        FullName = ValClassNameMap[It.first] + " " + FuncName;
        OCG.Parents[FullName].emplace(ParentName);
        OCG.Children[ParentName].emplace(FullName);
      }
      else
      {
        FullName = "NSObject " + FuncName;
        OCG.Parents[FullName].emplace(ParentName);
        OCG.Children[ParentName].emplace(FullName);
      }
    }

    // Do query
    std::set<std::string> Result;
    std::set<std::string> queryFuncs;
    std::cmatch m;
    for (auto &QueryFunc : OCCGQueryFunc)
    {
      outs() << "Query Func:\t" << QueryFunc << "\n";
      std::regex query_regex(QueryFunc);
      for (auto &It : OCG.Parents)
      {
        if (std::regex_search(It.first().str().c_str(), m, query_regex))
        {
          queryFuncs.emplace(It.first());
          outs() << "Caller exists for Callee " << It.first() << "\n";
        }
      }
    }

    const std::function<void(const std::string &)> queryResult =
        [&](const std::string &FuncName) -> void
    {
      if (OCG.Parents.count(FuncName) <= 0)
      {
        return;
      }
      for (auto &It : OCG.Parents[FuncName])
      {
        Result.emplace(It);
        queryResult(It);
      }
    };

    for (auto &queryFunc : queryFuncs)
    {
      queryResult(queryFunc);
      outs() << "Callee Chain of\t" << queryFunc<< ":\n";
      for (auto &It : Result)
      {
        outs() << It;
        if (It != *Result.end()) {
          outs()<< ", ";
        }
      }
      outs() << "\n";
      Result.clear();
    }
    
    closeLib(libm_hundle);
    return false;
  }

  string getClassNameFromGlobalV(GlobalVariable *GV){
    string classname = "";
    auto ClassNameStr = GV->getName();
    if (ClassNameStr.count("OBJC_CLASS") > 0)
    {
      std::regex re("global\\._OBJC_CLASS_\\$_(.+)_\\w+");
      std::smatch match;
      auto className = ClassNameStr.str();
      if (std::regex_match(className, match, re)) {
          className = match[1];
      }
      // auto Temp = ClassNameStr.drop_front(21);
      // auto Final = Temp.drop_back(6);
      auto Final = className;
      DEBUG(outs() << Final<< "\n";);
      classname = Final;
      return classname;
    }
    if (auto *subGV = dyn_cast<GlobalVariable>(GV->getOperand(0))){
      return getClassNameFromGlobalV(subGV);
    }
    classname = "NSObject";
    return classname;
  }

  string getClassNameFromLoad(CallInst *CI, LoadInst *LI){
    string classname = "";
    if (auto *GV = dyn_cast<GlobalVariable>(LI->getOperand(0))){
      classname = getClassNameFromGlobalV(GV);
    }

    if (auto *CII = dyn_cast<CastInst>(LI->getOperand(0)))
    {
        if (auto *ClassName = dyn_cast<GlobalVariable>(CII->getOperand(0))) {
          if (!ClassName)
          {
            DEBUG(outs() << "[Debug] Cannot resolve class name:\t"
                        << *LI->getOperand(0) << "\n";);
          }
          classname = getClassNameFromGlobalV(ClassName);
        }
    }
    if (auto *CE = dyn_cast<ConstantExpr>(LI->getOperand(0)))
    {
      if (auto *ClassName = dyn_cast<GlobalVariable>(CE->getOperand(0))) {
        if (!ClassName)
        {
          DEBUG(outs() << "[Debug] Cannot resolve class name:\t"
                      << *LI->getOperand(0) << "\n";);
        }
        classname = getClassNameFromGlobalV(ClassName);
      }
    }
    return classname;
  }

  void * getLibmHandle(const char *lib){
    // /root/workspace/toolchain/swift-5.9-RELEASE-ubuntu18.04/usr/lib/libswiftDemangle.so
    void * libm_handle = NULL;
    libm_handle = dlopen(lib, RTLD_LAZY);
    // 如果返回 NULL 句柄，表示无法找到对象文件，过程结束。否则的话，将会得到对象的一个句柄，可以进一步询问对象
    if (!libm_handle){
        // 如果返回 NULL 句柄,通过dlerror方法可以取得无法访问对象的原因
        return NULL;
    }
    return libm_handle;
  }

  std::string getSwiftDemangledName(void *libm_handle, std::string mangledName){
    // _$s10OCTestDemo5Test3C19identifierForVendoryyFTo
    typedef size_t (*swift_demangle_getDemangledName)(const char *MangledName, char *OutputBuffer, size_t Length);
    swift_demangle_getDemangledName fun_swift_demangle_getDemangledName;
    char *errorInfo;
    fun_swift_demangle_getDemangledName = (swift_demangle_getDemangledName)dlsym(libm_handle, "swift_demangle_getDemangledName");
    errorInfo = dlerror();// 调用dlerror方法，返回错误信息的同时，内存中的错误信息被清空
    if (errorInfo != NULL){
        errs()<<errorInfo<<"\n";
        return "";
    }
    size_t buffer_size = (*fun_swift_demangle_getDemangledName)(mangledName.c_str(), nullptr, 0);
    if (buffer_size <= 0){
      // that means it is not a swift mangle function
      return "";
    }
    buffer_size = buffer_size +1;
    std::vector<char>buffer(buffer_size);
    size_t result = (*fun_swift_demangle_getDemangledName)(mangledName.c_str(), buffer.data(), buffer_size);
    return std::string(buffer.data(), result);
  }

  typedef struct demangleInfo{
    std::string mode;
    std::string moduleName;
    std::string className;
    std::string functionName;
    std::string parameters;
    std::string returnType;
  };
  
  demangleInfo parseDemangledStr(std::string demangledName){
    std::regex pattern(R"((@nonobjc|@objc|static)?\s*(\w+)\.(\w+)\.(\w+)\(([\w\.\,]*)\)\s*(->\s*(\(\)|\w+\.\w+))?)");
    // "(^(@objc|static)?\s*(\w+)\.(\w+)\.(\w+)\(([\w\.\,]*)\)\s*(->\s*(\w+\.\w+))?)"
    std::regex patternTypeMeta(R"((?:type metadata accessor for|outlined destroy of) (\w+)\.(\w+))");
    std::smatch matches;
    demangleInfo demangleInfo;
    if (std::regex_match(demangledName, matches, pattern)) {
        demangleInfo.mode = matches[1].str();
        demangleInfo.moduleName = matches[2].str();
        demangleInfo.className = matches[3].str();
        demangleInfo.functionName = matches[4].str();
        demangleInfo.parameters = matches[5].str();
        demangleInfo.returnType = matches[6].str();

        // errs() << "Mode: " << demangleInfo.mode << "\n";
        // errs() << "Module name: " << demangleInfo.moduleName << "\n";
        // errs() << "Class name: " << demangleInfo.className << "\n";
        // errs() << "Function name: " << demangleInfo.functionName << "\n";
        // errs() << "Parameters: " << demangleInfo.parameters << "\n";
        // errs() << "Return type: " << demangleInfo.returnType << "\n";
    }
    std::smatch matches2;
    if (std::regex_match(demangledName, matches2, patternTypeMeta)){
        demangleInfo.moduleName = matches2[1].str();
        demangleInfo.className = matches2[2].str();
    }
    return demangleInfo;
  }

  void closeLib(void *libm_handle){
    dlclose(libm_handle);
  }

  std::string parseOCFunName(std::string ocString){
    if (ocString.find("-[") != std::string::npos | ocString.find("+[") != std::string::npos){
        ocString.erase(0,2);
        ocString.erase(ocString.end()-1);
    }
    return ocString;
  }

  // a function does nothing
  void nop()
  {
    exit(0);
  }
};

char OCCallGraphPass::ID = 0;
// Register as an analysis pass, satisfying Condition 3.
static RegisterPass<OCCallGraphPass> Y("occg", "Objective-C Call Graph Pass", false, true);

class OCCGChecker : public SrcMustReachSinkVulnerability
{
private:
  OCCallGraphPass *CG = nullptr;

public:
  OCCGChecker() : SrcMustReachSinkVulnerability("OCCGChecker") {}

  virtual void getAnalysisUsage(AnalysisUsage &AU)
  {
    // Requiring the assistant pass
    AU.addRequired<OCCallGraphPass>();
  }

  virtual void initializeAnalysis(Pass *P)
  {
    // Get the assistant pass
    CG = &P->getAnalysis<OCCallGraphPass>();
    // Ask the assistant pass to do something
    CG->nop();
  }

  virtual bool isSource(SEGNodeBase *Node, SEGSiteBase *Site) override
  {
    return false;
  }

  virtual bool isSink(SEGNodeBase *Node, SEGSiteBase *Site) override
  {
    return false;
  }
};

static VulnerabilityRegistry<OCCGChecker>
    X("ps-occg",
      "Run the checker detecting buffer overflow of scanf (OCCGChecker).",
      "ps-stable");