#include <string>
#include <iostream>
#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/AST/ASTContext.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/raw_ostream.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Lex/Lexer.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Refactoring.h"
#include "llvm/Support/CommandLine.h"
#include "clang/Tooling/Core/Replacement.h"
#include "clang/Lex/Lexer.h"
#include "clang/Basic/SourceManager.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Stmt.h"
#include <vector>
#include <set>
#include <unordered_map>
#include <regex>
#include <string>
#include<sstream>
#include<algorithm>
#include<iterator>
#include<fstream>
using namespace clang;
using namespace clang::ast_matchers;
using namespace clang::driver;
using namespace clang::tooling;
using namespace std;
#include<queue>

std::vector<string> labels;
std::vector<string> functions;
SourceLocation startOfFile;
int max_depth = 0;
static llvm::cl::OptionCategory MatcherSampleCategory("Matcher Sample");
int64_t first_id ;
std::unordered_map<int64_t, std::set<std::pair<int64_t, const clang::VarDecl*> > > var_mapf;
std::unordered_map<int64_t, std::set<std::pair<int64_t,const clang::VarDecl*> > > var_decl;
std::unordered_map<std::string, std::set<std::string> > variables;
std::unordered_map<string, std::set<std::pair<int64_t, string> > > functiondecl_listoflabels;
std::unordered_map<int64_t, std::vector<int64_t> > ParentsOfCompoundStmts; // greatest is the immediate function decl
std::unordered_map<int64_t, int64_t> vardecl_parent; // immediate CompoundStmt
std::unordered_map<int64_t, int64_t> callexpr_parent;
std::set<std::pair<unsigned, string> > update;

SourceLocation end_of_the_end(SourceLocation const & start_of_end, SourceManager &sm) {
  LangOptions lopt;
  return Lexer::getLocForEndOfToken(start_of_end, 0, sm, lopt);
}

int secondPassLabels = 0;

unordered_map<int64_t, std::set<std::pair<string, std::pair<string,string> > > >f_labelname_expr;

// callexpr_parent[id of call_expr] --> (id of the immediate)
unordered_map<int64_t, int> label_depth;
unordered_map<string, string > params;
// fid, labelname, parentcompundStatement, QualType, name of var
unordered_map<int64_t, string> CompoundStmtidLabelname;
unordered_map<string, unordered_map<string, int> > callablelabels;
unordered_map<int64_t, std::set<std::pair<int64_t, const VarDecl* > > > label_vars_refered;
std::set<string> nameOfHoistedLabels;

unordered_map<unsigned, std::pair<string, string> >  non_array_variables_used_in_program; // alfer renaming // safe
unordered_map<unsigned, std::pair<string, string> >  array_variables_used_in_program;  // safe
unsigned main_offset ;
unordered_map<int64_t,bool> modified_vardecls ;
unordered_map<string, bool> labeldeclsinmainfile;
// list name of all function decls defined in this file. after the labels have been hoisted.
unordered_map<string, std::set<std::pair<string, string> > > f_name_label_parent_label;
unordered_map<string, unordered_map<string, unsigned> > f_name_label_offset;


std::string ltrim(std::string str, const std::string& chars = "\t\n\v\f\r "){
    str.erase(0, str.find_first_not_of(chars));
    return str;
}
std::string rtrim(std::string str, const std::string& chars = "\t\n\v\f\r "){
    str.erase(str.find_last_not_of(chars) + 1);
    return str;
}
std::string trim(std::string str, const std::string& chars = "\t\n\v\f\r "){
    return ltrim(rtrim(str, chars), chars);
}
string getSourceTextt(SourceManager &sm, const Stmt * expr) {
  clang::LangOptions lopt;
  return clang::Lexer::getSourceText(clang::CharSourceRange(expr->getSourceRange(),true), sm, lopt).str();
}
string getSourceText(SourceManager &sm, const Expr * expr) {
  clang::LangOptions lopt;
  return clang::Lexer::getSourceText(clang::CharSourceRange(expr->getSourceRange(),true), sm, lopt).str();
}
string getSourceTextD(SourceManager &sm, const Decl * decl) {
  clang::LangOptions lopt;
  return clang::Lexer::getSourceText(clang::CharSourceRange(decl->getSourceRange(), true), sm, lopt).str();
}
string getTypeOfRecordDecl(string recordString) {
  string rettype = "";
  cout<<"record string is "<<recordString<<endl;
  std::istringstream buffer(recordString);
  std::vector<std::string> ret((std::istream_iterator<std::string>(buffer)),std::istream_iterator<std::string>());
  for(int i = 0; i<ret.size(); i++) {
      if(ret[i] == "struct") {
          rettype+=ret[i]+" ";
          int found = ret[i+1].find("{",0);
          if(found>=0 && found < ret[i+1].length()) {
              rettype+=ret[i+1].substr(0,found);
          }
          else rettype+=ret[i+1];
          cout<<"return type is "<<rettype<<endl;
          return rettype;
      }
  }
}
vector<string> splitString(string input) {
  std::istringstream buffer(input);
  std::vector<std::string> ret((std::istream_iterator<std::string>(buffer)),std::istream_iterator<std::string>());
  return ret;
}
set<string> usedvars;
class GenerateParams_CallExpr : public MatchFinder::MatchCallback {
public:
  GenerateParams_CallExpr(Rewriter &Rewrite) : Rewrite(Rewrite) {}

  virtual void run(const MatchFinder::MatchResult &Result) {
    const LabelStmt *labelStmtt = Result.Nodes.getNodeAs<LabelStmt>("labell");
    const DeclContext* decl = labelStmtt->getDecl()->getParentFunctionOrMethod();
    const FunctionDecl * fdecl = dyn_cast<FunctionDecl>(decl);

    std::set<std::pair<int64_t, const VarDecl*> >vars_refered = label_vars_refered[labelStmtt->getID(*Result.Context)];
    SourceManager &sm = Result.Context->getSourceManager();
    labeldeclsinmainfile[trim(labelStmtt->getDecl()->getNameAsString())] = 1;
    f_name_label_offset[trim(fdecl->getNameInfo().getName().getAsString())][trim(labelStmtt->getDecl()->getNameAsString())] = sm.getFileOffset(labelStmtt->getBeginLoc().getLocWithOffset(trim(labelStmtt->getDecl()->getNameAsString()).length()));

    std::vector<std::pair<int64_t, const VarDecl*>> v;  // later used to erase the vars from vars_refereds
    //llvm::outs()<<"test1 passed "<<'\n';
    bool parentfound = 0;
    string expr = "(";
    string exp1 = "(";
    std::set<std::pair<int64_t,const VarDecl*> > vars;
    auto pars = Result.Context->getParents(*labelStmtt);

    auto cp = Result.Context->getParents(*labelStmtt);
    // used to find the immediate parent ()
    const Stmt *tt = cp[0].get<Stmt>();
    const Decl * _n_n = cp[0].get<Decl>();

    // generates the label tree inside this function.
    while(!_n_n || !isa<TranslationUnitDecl>(_n_n)) {
      tt = cp[0].get<Stmt>();
      _n_n = cp[0].get<Decl>();
      if(tt) {
        if(isa<LabelStmt>(tt)) {
          const LabelStmt * label = dyn_cast<LabelStmt>(tt);
          f_name_label_parent_label[trim(fdecl->getNameInfo().getName().getAsString())].insert(make_pair(trim(labelStmtt->getDecl()->getNameAsString()),trim(label->getDecl()->getNameAsString())));
          f_name_label_parent_label[trim(fdecl->getNameInfo().getName().getAsString())].insert(make_pair(trim(labelStmtt->getDecl()->getNameAsString()),trim(labelStmtt->getDecl()->getNameAsString())));
          break;
        }
        cp = Result.Context->getParents(*tt);
      }
      else {
        const Decl * d = cp[0].get<Decl>();
        const FunctionDecl *fd = cp[0].get<FunctionDecl>();
          if(fd) {
            f_name_label_parent_label[trim(fd->getNameInfo().getName().getAsString())].insert(make_pair(trim(labelStmtt->getDecl()->getNameAsString()),"function"));
            f_name_label_parent_label[trim(fd->getNameInfo().getName().getAsString())].insert(make_pair(trim(labelStmtt->getDecl()->getNameAsString()), trim(labelStmtt->getDecl()->getNameAsString())));
            break;
          }
        cp = Result.Context->getParents(*d);
      }
      _n_n = cp[0].get<Decl>();
    }

    //llvm::outs()<<"test3 passed \n";

    const Stmt * t = pars[0].get<Stmt>();
    const Decl * _n = pars[0].get<Decl>();
    int depth = 0; // to calculate the maximum depth across all the label trees
    while(!_n || !isa<TranslationUnitDecl>(_n)) {
      depth ++ ;
      t = pars[0].get<Stmt>();
      _n = pars[0].get<Decl>();
      if(t) {
        while(!isa<CompoundStmt>(pars[0].get<Stmt>())) {
          t = pars[0].get<Stmt>();
          pars = Result.Context->getParents(*t);
        }
        if (isa<CompoundStmt>(pars[0].get<Stmt>())){
          vars = var_mapf[pars[0].get<CompoundStmt>()->getID(*Result.Context)];
          /*for (auto j: vars_refered){
            for(auto k: vars)
            if (j.first==k.first) {
              string labelname = CompoundStmtidLabelname[pars[0].get<CompoundStmt>()->getID(*Result.Context)];
              expr+= j.second->getType().getAsString()+" *"+(trim(j.second->getNameAsString()))+",";
              exp1 = "&"+trim(j.second->getNameAsString())+",";
              //To create the final struct
              if(labelname.compare("function")==(1-1)) //creating final struct
              params[labelname+to_string(fdecl->getID())]+=j.second->getType().getAsString()+" "+trim(j.second->getNameAsString())+";";
              v.push_back(j);
            }
          }
          for(auto j : v) {
            vars_refered.erase(j);
          }*/
        }
        pars = Result.Context->getParents(*t);
      }
      else {
        const Decl* d = pars[0].get<Decl>();
        const FunctionDecl * fd = pars[0].get<FunctionDecl>();

        if(fd) {
          functiondecl_listoflabels[trim(fd->getNameInfo().getName().getAsString())].insert(make_pair(labelStmtt->getID(*Result.Context), trim(labelStmtt->getDecl()->getNameAsString())));
          f_labelname_expr[fd->getID()].insert(make_pair(trim(labelStmtt->getDecl()->getNameAsString()), make_pair(expr,exp1)));
        }

        pars = Result.Context->getParents(*d);
        //llvm::outs()<<"no error in decl for labelStmt = "<<trim(labelStmtt->getDecl()->getNameAsString())<<'\n';
        //v.clear();
      }
      _n = pars[0].get<Decl>();
    }
    if(depth>max_depth) max_depth = depth;
  }

private:
  Rewriter &Rewrite;};  // Finds the label tree in each function.

unordered_map<unsigned, bool> unique_vardecl;
class RenameVars: public MatchFinder::MatchCallback {
public:
  RenameVars(Rewriter &Rewrite) :Rewrite(Rewrite) {}
  virtual void run(const MatchFinder::MatchResult &Result) {
    const DeclRefExpr* declRefExpr = Result.Nodes.getNodeAs<DeclRefExpr>("DeclRefExpr");
    string name = trim(declRefExpr->getNameInfo().getName().getAsString());
    declRefExpr->dump();
    const SourceManager * sm = Result.SourceManager;
    llvm::outs()<<"found decl ref expr with name = "<<name<<"\n";
    const ValueDecl* value = declRefExpr->getDecl();

    if(!isa<VarDecl>(value)) return;
    const VarDecl* vardecl = dyn_cast<VarDecl>(value);
    auto pars = Result.Context->getParents(*vardecl);

    if(!vardecl->isLocalVarDeclOrParm()) return;
    const DeclContext * dc = vardecl->getParentFunctionOrMethod();
    const FunctionDecl *fd = dyn_cast<FunctionDecl>(dc);

    int fid = fd->getID();
    const Stmt * t = pars[0].get<Stmt>();
    const Decl * _n = pars[0].get<Decl>();
    const Expr * e = pars[0].get<Expr>();
    bool isinsidecompoundstmt = 0;
    string forloopid = "";

    while(!_n || !isa<TranslationUnitDecl>(_n)) {
      t = pars[0].get<Stmt>();
      _n = pars[0].get<Decl>();
      if(t) {
        if(isa<ForStmt>(t)) {
          //const ForStmt * forStmt = dyn_cast<ForStmt>(t);
          //forloopid = to_string(forStmt->getID(*Result.Context));
          return; // no processing for for loops.
        }
        if(isa<CompoundStmt>(t)) {
          const CompoundStmt* labelStmt = dyn_cast<CompoundStmt>(t);
          int64_t id = labelStmt->getID(*Result.Context);
          isinsidecompoundstmt = 1;

          if(!unique_vardecl[sm->getFileOffset(vardecl->getLocation())]){
            update.insert(make_pair(sm->getFileOffset(vardecl->getLocation().getLocWithOffset(name.length())),to_string(id)+forloopid));
            usedvars.insert(name+to_string(id)+forloopid);
            unique_vardecl[sm->getFileOffset(vardecl->getLocation())] = true;
            if(vardecl->getType().getTypePtr()->isArrayType()) array_variables_used_in_program[sm->getFileOffset(vardecl->getLocation())]=(make_pair(name+to_string(id)+forloopid, value->getType().getAsString()));
            else non_array_variables_used_in_program[sm->getFileOffset(vardecl->getLocation())]= (make_pair(name+to_string(id)+forloopid,value->getType().getAsString()));
          }
          update.insert(make_pair(sm->getFileOffset(declRefExpr->getLocation().getLocWithOffset(name.length())), to_string(id)+forloopid));
          break;
        }
        pars = Result.Context->getParents(*t);
      }
      else {
        llvm::outs()<<"the parent is a decl\n";
        // hence need to insert into the struct using the functionid;
        break;
        if(_n) pars = Result.Context->getParents(*_n);
      }
    }
    if(!isinsidecompoundstmt){
      if(!unique_vardecl[sm->getFileOffset(vardecl->getLocation())]) {
        update.insert(make_pair(sm->getFileOffset(vardecl->getLocation().getLocWithOffset(name.length())),to_string(fid)+forloopid));
        usedvars.insert(name+to_string(fid)+forloopid);
        unique_vardecl[sm->getFileOffset(vardecl->getLocation())] = true;
        if(vardecl->getType().getTypePtr()->isArrayType()) array_variables_used_in_program[sm->getFileOffset(vardecl->getLocation())]= make_pair(name+to_string(fid)+forloopid, value->getType().getAsString());
        else non_array_variables_used_in_program[sm->getFileOffset(vardecl->getLocation())]=(make_pair(name+to_string(fid)+forloopid,value->getType().getAsString()));
      }
      update.insert(make_pair(sm->getFileOffset(declRefExpr->getLocation().getLocWithOffset(name.length())),to_string(fid)+forloopid));
      llvm::outs()<<"update has been written for this reference expr"<<"\n";
    }
}
private:
  Rewriter Rewrite;
}; // rename 1. Only declRefExpr
class RenameVars2 : public MatchFinder::MatchCallback{
public:
  RenameVars2(Rewriter &R): Rewrite(R){}
  virtual void run(const MatchFinder::MatchResult &result) {
    const SourceManager *sm = result.SourceManager;
    const VarDecl *vardecl = result.Nodes.getNodeAs<clang::VarDecl>("var");
    vardecl->dump();

    if(!vardecl->isLocalVarDeclOrParm()) return;
    if(sm->getFileID(vardecl->getBeginLoc()) != sm->getMainFileID()) return ;
    auto pars0 = result.Context->getParents(*vardecl);
    const Stmt * stmt = pars0[0].get<Stmt>();
    const DeclStmt * declstmt = 0;
    if(stmt)
    declstmt = dyn_cast<clang::DeclStmt>(stmt);
    auto pars = result.Context->getParents(*vardecl);
    string forloopid = "";
    const Stmt * t = pars[0].get<Stmt>();
    if(t) {

      while(!isa<CompoundStmt>(pars[0].get<Stmt>())) {
        t = pars[0].get<Stmt>();
        if(isa<ForStmt>(t)) {
          //const ForStmt * forStmt = dyn_cast<ForStmt>(t);
          //forloopid = to_string(forStmt->getID(*result.Context));
          return; // no processing for for loops.
        }
        pars = result.Context->getParents(*t);
      }
      if (isa<CompoundStmt>(pars[0].get<Stmt>())){
        var_mapf[pars[0].get<CompoundStmt>()->getID(*result.Context)].insert(make_pair(vardecl->getID(),vardecl));
        if(!unique_vardecl[sm->getFileOffset(vardecl->getLocation())]) {
          unique_vardecl[sm->getFileOffset(vardecl->getLocation())] = true;
          // if not used, then no need to make an entry in global struct.
          if(vardecl->getType().getTypePtr()->isArrayType()) array_variables_used_in_program[sm->getFileOffset(vardecl->getLocation())]=(make_pair(trim(vardecl->getNameAsString())+to_string(pars[0].get<CompoundStmt>()->getID(*result.Context))+forloopid, vardecl->getType().getAsString()));
          else non_array_variables_used_in_program[sm->getFileOffset(vardecl->getLocation())]= (make_pair(trim(vardecl->getNameAsString())+to_string(pars[0].get<CompoundStmt>()->getID(*result.Context))+forloopid, vardecl->getType().getAsString()));
          update.insert(make_pair(sm->getFileOffset(vardecl->getLocation().getLocWithOffset(trim(vardecl->getNameAsString()).length())), to_string(pars[0].get<CompoundStmt>()->getID(*result.Context))+forloopid));
          //Rewrite.InsertTextAfter(vardecl->getLocation().getLocWithOffset(trim(vardecl->getNameAsString()).length()),to_string(pars[0].get<CompoundStmt>()->getID(*result.Context))+forloopid);
          //Rewrite.overwriteChangedFiles();
        }
      }
    }
    else {
      const Decl* d = pars[0].get<Decl>();
      if(d){
        var_decl[d->getID()].insert(make_pair(vardecl->getID(), vardecl));
        if(!unique_vardecl[sm->getFileOffset(vardecl->getLocation())]) {
          unique_vardecl[sm->getFileOffset(vardecl->getLocation())]=true;
          // if not used, then no need to make an entry in global struct.
          if(vardecl->getType().getTypePtr()->isArrayType()) array_variables_used_in_program[sm->getFileOffset(vardecl->getLocation())]=(make_pair(trim(vardecl->getNameAsString())+to_string(pars[0].get<CompoundStmt>()->getID(*result.Context))+forloopid, vardecl->getType().getAsString()));
          else non_array_variables_used_in_program[sm->getFileOffset(vardecl->getLocation())]= (make_pair(trim(vardecl->getNameAsString())+to_string(pars[0].get<CompoundStmt>()->getID(*result.Context))+forloopid,vardecl->getType().getAsString()));
          update.insert(make_pair(sm->getFileOffset(vardecl->getLocation().getLocWithOffset(trim(vardecl->getNameAsString()).length())), to_string(d->getID())+forloopid));
          //Rewrite.InsertTextAfter(vardecl->getLocation().getLocWithOffset(trim(vardecl->getNameAsString()).length()),to_string(d->getID())+forloopid);
          //Rewrite.overwriteChangedFiles();
        }
      }
    }
    llvm::outs()<<"no error till now"<<'\n';
    //Rewrite.overwriteChangedFiles();
  }
private:
  Rewriter Rewrite;}; // rename 2. No file rewrite. Only collect data.

unordered_map<int64_t, bool> whetherassignmentdone_varid_bool;  // for one ast, the varid does not change.
std::set<std::pair<unsigned, string> > decls;
class FindParentsOfDecl_rename3 : public MatchFinder::MatchCallback{  // does not match the parameters.
public:
  // to detect the renamed vardecl and generate the assignment statements only.
  FindParentsOfDecl_rename3(Rewriter &R): Rewrite(R){}
  virtual void run(const MatchFinder::MatchResult &result) {
    const VarDecl *vardecl = result.Nodes.getNodeAs<clang::VarDecl>("rename3");
    if(!vardecl->isLocalVarDecl()) return; /**Shankar*/
    const SourceManager *sm = result.SourceManager;
    const DeclStmt * declstmt = result.Nodes.getNodeAs<DeclStmt>("declStmt");
    vardecl->dump();
    if(!usedvars.count(trim(vardecl->getNameAsString()))) return; // usedvars is a set because all variables are necessarily unique;
    if(declstmt && !whetherassignmentdone_varid_bool[vardecl->getID()]) {
      whetherassignmentdone_varid_bool[vardecl->getID()] = true;
      if(vardecl->getType().getTypePtr()->isArrayType()){
        decls.insert(make_pair(sm->getFileOffset(declstmt->getEndLoc().getLocWithOffset(1)),"compiler_."+trim(vardecl->getNameAsString())+"="+trim(vardecl->getNameAsString())+";"));
      }
      else{
        decls.insert(make_pair(sm->getFileOffset(declstmt->getEndLoc().getLocWithOffset(1)),"compiler_."+trim(vardecl->getNameAsString())+"=&"+trim(vardecl->getNameAsString())+";"));
      }
    }

    //auto pars = result.Context->getParents(*vardecl);
    //FileID fileid = sm->getMainFileID();
    //if(sm->getFileID(vardecl->getBeginLoc()) != fileid) return;
    //const Stmt * t = pars[0].get<Stmt>();
    /*
    if(t) {
      while(!isa<CompoundStmt>(pars[0].get<Stmt>())) {
        t = pars[0].get<Stmt>();
        pars = result.Context->getParents(*t);
        if(t) { // detect if this is a decl statement or not.
          const DeclStmt * declstmt = dyn_cast<clang::DeclStmt>(t); // t cannot be null
          if(declstmt && !whetherassignmentdone_varid_bool[vardecl->getID()]) {
            whetherassignmentdone_varid_bool[vardecl->getID()] = true;
            if(vardecl->getType().getTypePtr()->isArrayType()){
              decls.insert(make_pair(sm->getFileOffset(declstmt->getEndLoc().getLocWithOffset(1)),";compiler_."+trim(vardecl->getNameAsString())+"="+trim(vardecl->getNameAsString())+";"));
            }
            else{
              decls.insert(make_pair(sm->getFileOffset(declstmt->getEndLoc().getLocWithOffset(1)),";compiler_."+trim(vardecl->getNameAsString())+"=&"+trim(vardecl->getNameAsString())+";"));
            }
            //Rewrite.overwriteChangedFiles();
          }
        }
      }
      if (isa<CompoundStmt>(pars[0].get<Stmt>())){
        var_mapf[pars[0].get<CompoundStmt>()->getID(*result.Context)].insert(make_pair(vardecl->getID(),vardecl));
      }
    }
    else {
      const Decl* d = pars[0].get<Decl>();
      if(d)
      var_decl[d->getID()].insert(make_pair(vardecl->getID(), vardecl));
    }
    */
  }
private:
  Rewriter Rewrite;}; // stage3. Detects the declstmt and writes assignment

class FunctionDeclStmtHandler : public MatchFinder::MatchCallback{
  public:
    FunctionDeclStmtHandler(Rewriter &R): Rewrite(R){}
    virtual void run(const MatchFinder::MatchResult &result) {
      SourceManager &sm = result.Context->getSourceManager();
      const FunctionDecl * fdecl = result.Nodes.getNodeAs<FunctionDecl>("f_decl");
      const FunctionDecl * function = result.Nodes.getNodeAs<FunctionDecl>("Shiva");
      const DeclStmt * declstmt = result.Nodes.getNodeAs<DeclStmt>("DeclParent");
      Rewrite.RemoveText(declstmt->getSourceRange());
      Rewrite.InsertTextBefore(function->getBeginLoc(), getSourceTextt(sm, declstmt));
      Rewrite.overwriteChangedFiles();
    }
  private:
  Rewriter Rewrite;}; // rename 2. No file rewrite. Only collect data.

unordered_map<string, set<string> > function_decl_params;
class ParameterDeclHandler : public MatchFinder::MatchCallback {
  public:
    ParameterDeclHandler(Rewriter &R):Rewrite(R){}
    virtual void run(const MatchFinder::MatchResult &Result) {
      const CompoundStmt * compoundStmt = Result.Nodes.getNodeAs<CompoundStmt>("ParameterCompoundStmt");
      const FunctionDecl * functiondecl = Result.Nodes.getNodeAs<FunctionDecl>("parameterF");
      llvm::outs()<<"***************************************************************************************************************************************************the function is "<<trim(functiondecl->getNameInfo().getName().getAsString())<<"\n";
      for(auto a : function_decl_params[trim(functiondecl->getNameInfo().getName().getAsString())])
        Rewrite.InsertTextAfter(compoundStmt->getLBracLoc().getLocWithOffset(1),a);
      Rewrite.overwriteChangedFiles();
    }
  private:
    Rewriter &Rewrite;
  };
unordered_map<unsigned, set<pair<unsigned, string> > > scope_record_type;
unordered_map<unsigned, int64_t> recordDecl_offset_scopeid;
unordered_map<unsigned, set<pair< string /*declaration of variable/field*/, pair< unsigned /*start of vardecl/fieldDecl*/, unsigned /*end of vardecl/fieldDecl*/ > > > > Declarations_refereing_struct;
unordered_map<unsigned /*scope offset*/, set<pair<pair<string /*recordtype*/, string /*recordString*/>, pair<unsigned /*beginoffset of recorddecl*/, unsigned /*end offset of recordecl*/> > > > recordDeclsinScope;
class RecordDecl1 : public MatchFinder::MatchCallback{
public:
  RecordDecl1(Rewriter &R): Rewrite(R){}
  virtual void run(const MatchFinder::MatchResult &Result) {
    // contains both the record decl and a parent compound statement.
    const RecordDecl * recordDecl = Result.Nodes.getNodeAs<RecordDecl>("recordecl");
    const CompoundStmt * compoundStmt = Result.Nodes.getNodeAs<CompoundStmt>("scope");

    SourceManager &sm = Result.Context->getSourceManager();
    const DeclStmt * declStmt = Result.Nodes.getNodeAs<DeclStmt>("enclosingDeclStmt");
    SourceLocation recordbegin = declStmt->getBeginLoc();
    SourceLocation recordEnd = declStmt->getEndLoc();
    unsigned offsetrecordbegin = sm.getFileOffset(recordbegin);
    unsigned offsetrecordend = sm.getFileOffset(recordEnd);
    recordDecl_offset_scopeid[offsetrecordbegin] = compoundStmt->getID(*Result.Context);
    string recorddecltext = getSourceTextD(sm, recordDecl);
    recordDeclsinScope[sm.getFileOffset(compoundStmt->getLBracLoc())].insert(make_pair(make_pair(getTypeOfRecordDecl(recorddecltext), recorddecltext), make_pair(offsetrecordbegin, offsetrecordend)));
    scope_record_type[sm.getFileOffset(compoundStmt->getLBracLoc())].insert(make_pair(offsetrecordbegin,getTypeOfRecordDecl(recorddecltext)));
  }
private:
  Rewriter &Rewrite;
};// lists all the record decls in each scope.
class RecordDecl2 : public MatchFinder::MatchCallback{  // lists all the field decls and the types they refer to in their scope
public:
  RecordDecl2(Rewriter &R): Rewrite(R) {}
  virtual void run(const MatchFinder::MatchResult &Result) {
    // print the field decls, thier parents types and the types they refer to.
    const FieldDecl * fieldDecl = Result.Nodes.getNodeAs<FieldDecl>("field");
    const CompoundStmt * compoundStmt = Result.Nodes.getNodeAs<CompoundStmt>("scope");
    const RecordDecl * record = fieldDecl->getParent();
    SourceManager &sm = Result.Context->getSourceManager();

    bool found = false;
    for(auto a : splitString(fieldDecl->getType().getAsString())) {
      if(a=="struct") found = true;
    }
    if(!found) return;
    string fieldtype = getTypeOfRecordDecl(fieldDecl->getType().getAsString());
    string fieldeclString = getSourceTextD(sm, fieldDecl);
    unsigned offsetBeginField = sm.getFileOffset(fieldDecl->getBeginLoc());
    unsigned offsetEndField = sm.getFileOffset(fieldDecl->getEndLoc());
    unsigned recordoffset = 0;
    for(auto a : recordDeclsinScope[sm.getFileOffset(compoundStmt->getLBracLoc())]) {
      if(a.first.first == fieldtype) {
        recordoffset = a.second.first;
        break;
      }
    }
    Declarations_refereing_struct[recordoffset].insert(make_pair(fieldeclString, make_pair(offsetBeginField, offsetEndField)));
  }
private:
  Rewriter &Rewrite;
};
class RecordDecl3 : public MatchFinder::MatchCallback{  // lists all the variable decls and the types they refer to in their scope
public:
  RecordDecl3(Rewriter &R): Rewrite(R) {}
  virtual void run(const MatchFinder::MatchResult &Result) {
    // print the field decls, thier parents types and the types they refer to.
    const VarDecl * varDecl = Result.Nodes.getNodeAs<VarDecl>("vardecl");
    const CompoundStmt * compoundStmt = Result.Nodes.getNodeAs<CompoundStmt>("scope");
    const DeclStmt * declStmt = Result.Nodes.getNodeAs<DeclStmt>("declStmt");
    SourceManager &sm = Result.Context->getSourceManager();

    //if(splitString(varDecl->getType().getAsString())[0]!="struct") return;
    bool found = false;
    for(auto a : splitString(varDecl->getType().getAsString())){
      if(a=="struct") found = true;
    }
    if(!found) return;
    string vartype = getTypeOfRecordDecl(varDecl->getType().getAsString());
    string vardeclString = getSourceTextt(sm, declStmt);
    unsigned offsetBegin = sm.getFileOffset(declStmt->getBeginLoc());
    unsigned offsetEnd = sm.getFileOffset(declStmt->getEndLoc());
    unsigned recordoffset = 0;
    for(auto a : recordDeclsinScope[sm.getFileOffset(compoundStmt->getLBracLoc())]) {
      if(a.first.first == vartype) {
        recordoffset = a.second.first;
        break;
      }
    }
    Declarations_refereing_struct[recordoffset].insert(make_pair(vardeclString, make_pair(offsetBegin, offsetEnd)));
  }
private:
  Rewriter &Rewrite;
};
set<pair<unsigned, pair<string, unsigned> > > record_decl_definitions;
class RecordDeclHandler : public MatchFinder::MatchCallback{
public:
  RecordDeclHandler(Rewriter &R):Rewrite(R) {}
  virtual void run(const MatchFinder::MatchResult &Result) {
    const RecordDecl * recordDecl = Result.Nodes.getNodeAs<RecordDecl>("recordDecl");
    const DeclStmt * declStmt = Result.Nodes.getNodeAs<DeclStmt>("declStmt");
    const FunctionDecl * fdecl = Result.Nodes.getNodeAs<FunctionDecl>("parentfunction");
    SourceManager &sm = Result.Context->getSourceManager();
    SourceRange range = declStmt->getSourceRange();
    string record = getSourceTextt(sm, declStmt);
    Rewrite.RemoveText(range);
    Rewrite.InsertTextBefore(fdecl->getBeginLoc(), record);
    Rewrite.overwriteChangedFiles();
    //record_decl_definitions.insert(make_pair(sm.getFileOffset(declStmt->getBeginLoc()), make_pair(getSourceTextt(sm,declStmt),sm.getFileOffset(declStmt->getEndLoc()))));
  }
private:
  Rewriter Rewrite;
};
unordered_map<unsigned, std::pair<unsigned,string>> updatecallexpr;
unordered_map<string, int64_t> fname_id;/**To be used by HoistLabels*/
class ModifyCallExpr : public MatchFinder::MatchCallback {
public:
  ModifyCallExpr(Rewriter &Rewrite) : Rewrite(Rewrite) {}

  virtual void run(const MatchFinder::MatchResult &Result) {
    const FunctionDecl* functionDecl = Result.Nodes.getNodeAs<FunctionDecl>("function");
    SourceManager &sm = Result.Context->getSourceManager();
    FileID fileid = sm.getMainFileID();
    if(sm.getFileID(functionDecl->getBeginLoc()) != fileid) return;
    if(functionDecl->doesThisDeclarationHaveABody()) {
      fname_id[trim(functionDecl->getNameInfo().getName().getAsString())] = functionDecl->getID();
    }
  }

private:
  Rewriter &Rewrite;
};

// puts the labels onto the top after converting them to functions.
std::set<string> function_decls;
std::set<std::pair<unsigned, std::pair<unsigned, string> > > updatehoistreplace;
class HoistLabels: public MatchFinder::MatchCallback{
  public:
    HoistLabels(Rewriter &Rewrite) : Rewrite(Rewrite) {}
    virtual void run(const MatchFinder::MatchResult &Result) {
      const LabelStmt* labelh = Result.Nodes.getNodeAs<LabelStmt>("label_leaf");
      const FunctionDecl * parent_function = Result.Nodes.getNodeAs<FunctionDecl>("parent_function"); // o

      SourceManager &sm = Result.Context->getSourceManager();
      llvm::outs()<<"label name to be hoisted is "<<trim(labelh->getDecl()->getNameAsString());

      int count = 0; // counts no. of children which are labels to test if this is a leaf
      for (auto i = labelh->child_begin(), e = labelh->child_end(); i != e; ++i) {
        for (auto j = i->child_begin(), f = i->child_end(); j != f; ++j) {
          if(isa<LabelStmt>(*j)) count++;
        }
      }

      if(!count) { // hence a leaf
        SourceRange decl_range(labelh->getSourceRange());  // modified with labelh to labelh->getDecl();
        SourceLocation decl_begin(decl_range.getBegin());
        SourceLocation decl_start_end(decl_range.getEnd());
        SourceLocation decl_end_end(end_of_the_end(decl_start_end,sm));

        SourceRange decl_range_decl(labelh->getDecl()->getSourceRange());  // modified with labelh to labelh->getDecl();
        SourceLocation decl_begin_decl(decl_range_decl.getBegin());
        SourceLocation decl_start_end_decl(decl_range_decl.getEnd());
        SourceLocation decl_end_end_decl(end_of_the_end(decl_start_end_decl,sm));

        const char * buff_begin(sm.getCharacterData(decl_begin));
        const char * buff_end(sm.getCharacterData(decl_end_end));
        std::string label_string(buff_begin, buff_end); // print it to get the actual label contents.
        llvm::outs()<<"label string unmodified\n"<<label_string<<"\n";

        //modified the decl_end_end with decl_start_end
        unsigned int const decl_length = sm.getFileOffset(decl_end_end)-sm.getFileOffset(decl_begin);
        unsigned int const decl_length_decl = sm.getFileOffset(decl_start_end_decl)-sm.getFileOffset(decl_begin_decl);
        //string name = trim(label_string.substr(0,label_string.find(":",0)));
        string name = trim(labelh->getDecl()->getNameAsString());
        llvm::outs()<<"name of the  label (space) is "<<name<<"\n";

        //functiondecl_listoflabels[fd->getID()].insert(make_pair(labelh->getID(*Result.Context), trim(labelh->getDecl()->getNameAsString())));

        std::regex e("([a-zA-Z_][0-9a-zA-Z_]*)+[ ]*[:][ ]*[{]");
        smatch m;
        regex_search(label_string, m,e);
        // modify only the first occurance (also since this is the leaf, so only one occurance).
        // assume : the function call expr having a labelname does correspond to a labelname.
        label_string.replace(label_string.find(m[0].str()),m[0].str().length(),name+to_string(fname_id[trim(parent_function->getNameInfo().getName().getAsString())])+"(){");
        function_decls.insert(name+to_string(fname_id[trim(parent_function->getNameInfo().getName().getAsString())]));

        //label_string.replace(label_string.find(name+":",0), name.length()+2, name+expr+"){");
        // check if the function is callable. If not, then replace it with a call to the label with its params.
        string labelname = trim(labelh->getDecl()->getNameAsString());
        nameOfHoistedLabels.insert(labelname+to_string(parent_function->getID()));
        Rewrite.RemoveText(decl_begin_decl, decl_length); // replace the leaf label with the null string.
        Rewrite.InsertTextBefore(parent_function->getBeginLoc(), "void "+label_string+"\n");
        Rewrite.overwriteChangedFiles();
        return;
      }
    }

  private:
    Rewriter &Rewrite;
  };

unordered_map<unsigned, string> renamebeforeuse;
class RenameVarUse: public MatchFinder::MatchCallback {
public:
  RenameVarUse(Rewriter &Rewrite) :Rewrite(Rewrite) {}
  virtual void run(const MatchFinder::MatchResult &Result) {
    const DeclRefExpr* declRefExpr = Result.Nodes.getNodeAs<DeclRefExpr>("DeclRefExpr2");
    const DeclRefExpr * valu = Result.Nodes.getNodeAs<DeclRefExpr>("returnedvalue");
    const SourceManager * sm = Result.SourceManager;
    auto result = Result;
    // check if it has a parent for loop
    // search for parent.
    if(valu) {
      valu->dump();
      //FileID fileid = sm->getMainFileID();
      //if(sm->getFileID(valu->getLocation()) != fileid) return;

      const ValueDecl * valuee = valu->getDecl();
      if(!isa<VarDecl>(valuee)) return;
      const VarDecl * vardecl = dyn_cast<VarDecl>(valuee);
      if(!vardecl->isLocalVarDeclOrParm()) return;
      // test if vardecl does not have for loop as parent.
      auto parsfor = result.Context->getParents(*vardecl);
      string forloopid = "";
      const Stmt * t = parsfor[0].get<Stmt>();
      if(t) {

        while(!isa<CompoundStmt>(parsfor[0].get<Stmt>())) {
          t = parsfor[0].get<Stmt>();
          if(isa<ForStmt>(t)) {
            //const ForStmt * forStmt = dyn_cast<ForStmt>(t);
            //forloopid = to_string(forStmt->getID(*result.Context));
            return; // no processing for for loops.
          }
          parsfor = result.Context->getParents(*t);
        }
      }
      vardecl->dump();
      if(valu->getType().getTypePtr()->isArrayType()) { // before return statement.
        renamebeforeuse[sm->getFileOffset(valu->getLocation())] = "compiler2.";
      }
      else {
        renamebeforeuse[sm->getFileOffset(valu->getLocation())] = "(*compiler2.";
        renamebeforeuse[sm->getFileOffset(valu->getLocation().getLocWithOffset(trim(valu->getNameInfo().getName().getAsString()).length()))] = ")";
      }
      return;
    }
    if(declRefExpr) {
      declRefExpr->dump();
    string name = trim(declRefExpr->getNameInfo().getName().getAsString());
    //FileID fileid = sm->getMainFileID();
    //if(sm->getFileID(declRefExpr->getLocation()) != fileid) return;

    // test if this is an array variable. If this is a reference to a variable statement, it means that its' parents' parent should be ArraySubscriptExpr
    const ValueDecl* value = declRefExpr->getDecl();
    llvm::outs()<<"inside declrefexpr with name = "<<name<<'\n';

    if(!isa<VarDecl>(value)) return;
    const VarDecl * vardecl = dyn_cast<VarDecl>(value);
    if(!vardecl->isLocalVarDeclOrParm()) return;
    auto parsfor = result.Context->getParents(*vardecl);
    string forloopid = "";
    const Stmt * t = parsfor[0].get<Stmt>();
    if(t) {

      while(!isa<CompoundStmt>(parsfor[0].get<Stmt>())) {
        t = parsfor[0].get<Stmt>();
        if(isa<ForStmt>(t)) {
          //const ForStmt * forStmt = dyn_cast<ForStmt>(t);
          //forloopid = to_string(forStmt->getID(*result.Context));
          return; // no processing for for loops.
        }
        parsfor = result.Context->getParents(*t);
      }
    }
    vardecl->dump();
    if(declRefExpr->getType().getTypePtr()->isArrayType()) {
      renamebeforeuse[sm->getFileOffset(declRefExpr->getLocation())] = "compiler_.";
      llvm::outs()<<"renamed"<<"\n";
      //Rewrite.InsertTextBefore(declRefExpr->getLocation(),"compiler_.");
    }
    else {
      renamebeforeuse[sm->getFileOffset(declRefExpr->getLocation())] = "(*compiler_.";
      renamebeforeuse[sm->getFileOffset(declRefExpr->getLocation().getLocWithOffset(trim(declRefExpr->getNameInfo().getName().getAsString()).length()))] = ")";
      llvm::outs()<<"renamed"<<"\n";
      //Rewrite.InsertTextBefore(declRefExpr->getLocation(),"*compiler_.");
    }
  }
    //Rewrite.overwriteChangedFiles();
}
private:
  Rewriter Rewrite;
};

std::set<std::pair<unsigned, string> > structInsertafter2;
std::set<std::pair<unsigned, unsigned> > structremove1;
class StructureHandler : public MatchFinder::MatchCallback {
public:
  StructureHandler(Rewriter &R ) : Rewrite(R) {}
  virtual void run(const MatchFinder::MatchResult &Result ) {
    const RecordDecl * record = Result.Nodes.getNodeAs<RecordDecl>("struct");
    record->dump();
    SourceManager &sm = Result.Context->getSourceManager();
    //FileID fileid = sm.getMainFileID();
    //if(sm.getFileID(record->getBeginLoc()) != fileid) return;
    //if(sm.getFileID(record->getDefinition()->getBeginLoc())!=fileid) return;
    RecordDecl * defn = record->getDefinition();
    auto pars = Result.Context->getParents(*defn);
    const DeclStmt* decl = pars[0].get<DeclStmt>();
    //const DeclStmt * decl;
    //if(stmt) decl = dyn_cast<clang::DeclStmt>(stmt);
    cout<<"struct handler"<<" no error"<<endl;
    if(decl) llvm::outs()<<"Declaration statement found "<<'\n';
    else return;
    SourceRange decl_range(decl->getSourceRange());  // modified with labelh to labelh->getDecl();
    llvm::outs()<<"test1\n";
    SourceLocation decl_begin(decl_range.getBegin());
    SourceLocation decl_start_end(decl_range.getEnd());
    SourceLocation decl_end_end(end_of_the_end(decl_start_end,sm));
    llvm::outs()<<"test2\n";
    const char * buff_begin(sm.getCharacterData(decl_begin));
    const char * buff_end(sm.getCharacterData(decl_end_end));
    std::string record_string(buff_begin, buff_end);
    llvm::outs()<<"test3\n";
    //modified the decl_end_end with decl_start_end
    unsigned int const decl_length = sm.getFileOffset(decl_end_end)-sm.getFileOffset(decl_begin)+1;
    structInsertafter2.insert(make_pair(sm.getFileOffset(decl_begin),record_string));
    structremove1.insert(make_pair(sm.getFileOffset(decl_begin),decl_length));
    //llvm::outs()<<"before replacing text\n";
    //Rewrite.InsertTextBefore(decl_begin,"/*");
    //Rewrite.InsertTextAfter(decl_end_end, "*/");
    //Rewrite.overwriteChangedFiles();
  }

private:
  Rewriter Rewrite;
};

unordered_map<unsigned, string> renameArray;
std::set<std::pair<unsigned,unsigned> >commentArray;
class MultidimensionalArray : public MatchFinder::MatchCallback {
public:
  MultidimensionalArray(Rewriter &R) : Rewrite(R) {}
  virtual void run(const MatchFinder::MatchResult &Result) {
    const DeclRefExpr * declRefExpr = Result.Nodes.getNodeAs<DeclRefExpr>("multiarray");
    //Rewrite.InsertTextAfter(declRefExpr->getEndLoc(), "/* this is the reference*/");
    //Rewrite.overwriteChangedFiles();
    SourceManager &sm = Result.Context->getSourceManager();
    if(!declRefExpr->getType().getTypePtr()->isArrayType()) return;
    const VarDecl * vardecl;
    if(isa<VarDecl>(declRefExpr->getDecl())) vardecl = dyn_cast<VarDecl>(declRefExpr->getDecl());
    if(vardecl && !vardecl->hasLocalStorage()) return;
    llvm::errs()<<" *****************************************************Array is found with type = "<<declRefExpr->getType().getAsString()<<"*************************************************\n";
    string type = trim(declRefExpr->getType().getAsString());
    int n = std::count(type.begin(), type.end(), '*') + std::count(type.begin(), type.end(), '[');
    llvm::outs()<<"*************************************************** n is "<<n<<" ********************************** \n";
    auto pars = Result.Context->getParents(*declRefExpr);
    auto value = declRefExpr->getDecl();
    const FieldDecl * rdecl;
    if(value)
      rdecl = dyn_cast<FieldDecl>(value); // if the array is a field decl, simply return;
    if(rdecl) return;

    llvm::outs()<<"name of var is "<<trim(declRefExpr->getNameInfo().getName().getAsString())<<" type is "<<type<<"\n";
    int n1 = n;
    std::vector<string> dimensions ;
    //clang::LangOptions lopt;
    auto declType=(declRefExpr->getType());
    while(--n1) {
      llvm::outs()<<"n1 is "<<n1<<" \n";
      const VariableArrayType * vt = Result.Context->getAsVariableArrayType(declType);
      if(vt) {
        llvm::outs()<<"It is a varible array type\n";
        const Expr* ex = vt->getSizeExpr();
        dimensions.push_back(getSourceText(sm, ex));
        llvm::outs()<<"Source text returned successfully\n";
        declType = vt->getElementType();
      }
      else {
        const ConstantArrayType *ct = Result.Context->getAsConstantArrayType(declType);
        llvm::outs()<<"it is a constant array type"<<'\n';
        dimensions.push_back(to_string(ct->getSize().getSExtValue()));
        llvm::outs()<<"the value is pushed in the dimension"<<"\n";
        declType = ct->getElementType();
      }
    }
    std::vector<string>indices;
    const ArraySubscriptExpr *ar;
    while(n) {
      const Expr * expr = pars[0].get<Expr>();
      if(expr){
        llvm::outs()<<"expression found\n";
      if(isa<ArraySubscriptExpr>(expr)){
        llvm::outs()<<"it prints that the expression is indeed an ArraySubscriptExpr\n";
        ar = dyn_cast_or_null<ArraySubscriptExpr>(expr);
        if(ar) {
          llvm::outs()<<"there is an array reference expression\n";
          const Expr * id = ar->getIdx();
          llvm::outs()<<"index is generated \n";
          n--; indices.push_back(getSourceText(sm, id));
          llvm::outs()<<"Source text returned successfully\n";
        }
      }
      }
      else break;
      pars = Result.Context->getParents(*expr);
    }

    llvm::outs()<<"out of the upper while loop\n The indices length is "<<to_string(indices.size())<<'\n';
    string renameexpr = "(compiler_."+trim(declRefExpr->getNameInfo().getName().getAsString())+"[";
    if(indices.size()==0) {
      renameexpr="compiler_."+trim(declRefExpr->getNameInfo().getName().getAsString()); // if array is passed as function argument.
    }
    else {
      for(int i = 0; i<indices.size()-1; i++) {
        renameexpr+=indices[i]+"*(";
        for(int j = i+1; j<dimensions.size()-1; j++ ) {
          renameexpr+=dimensions[j]+"*";
        }
        renameexpr+=dimensions[dimensions.size()-1];
        renameexpr+=")+";
      }
      renameexpr+=indices[indices.size()-1]+"])";
      llvm::outs()<<"modified the expression\n";
    }
    if(indices.size()==0){

      commentArray.insert(make_pair(sm.getFileOffset(declRefExpr->getBeginLoc()),sm.getFileOffset(declRefExpr->getLocation().getLocWithOffset(trim(declRefExpr->getNameInfo().getName().getAsString()).length()))));
      renameArray[sm.getFileOffset(declRefExpr->getLocation().getLocWithOffset(trim(declRefExpr->getNameInfo().getName().getAsString()).length()))] = renameexpr;
    }
    else {
      commentArray.insert(make_pair(sm.getFileOffset(declRefExpr->getBeginLoc()), sm.getFileOffset(ar->getRBracketLoc().getLocWithOffset(1))));
      renameArray[sm.getFileOffset(ar->getRBracketLoc().getLocWithOffset(1))] = renameexpr;
    }
  }
private:
  Rewriter Rewrite;
};
class RecursionHandler_1 : public MatchFinder::MatchCallback {
public:
  RecursionHandler_1(Rewriter &R):Rewrite(R){}
  virtual void run(const MatchFinder::MatchResult &Result) {
    const CompoundStmt * compoundStmt = Result.Nodes.getNodeAs<CompoundStmt>("recursion1");
    const FunctionDecl * parentFunction = Result.Nodes.getNodeAs<FunctionDecl>("parent_function");
    string assignment = "";
    for(unsigned i = 0; i<parentFunction->getNumParams(); i++) {
      const ParmVarDecl * paramvardecl = parentFunction->getParamDecl(i);
      if(paramvardecl->getType().getTypePtr()->isArrayType()){
        assignment+="compiler_."+trim(paramvardecl->getNameAsString())+"="+trim(paramvardecl->getNameAsString())+";";
      }
      else{
        assignment+="compiler_."+trim(paramvardecl->getNameAsString())+"=&"+trim(paramvardecl->getNameAsString())+";";
      }
    }
    Rewrite.InsertTextAfter(compoundStmt->getLBracLoc().getLocWithOffset(1),"struct compiler compiler1 = compiler_;"+assignment);
    Rewrite.InsertTextBefore(compoundStmt->getEndLoc(), "compiler_ = compiler1;");
    Rewrite.overwriteChangedFiles();
  }
private:
  Rewriter Rewrite;
};

std::set<string> listofallfdecls;
class RecursionHandler_2 : public MatchFinder::MatchCallback {
public:
  RecursionHandler_2(Rewriter &R): Rewrite(R){}
  virtual void run(const MatchFinder::MatchResult &Result) {
    const ReturnStmt * returnStmt = Result.Nodes.getNodeAs<ReturnStmt>("recursion2");
    SourceManager &sm = Result.Context->getSourceManager();
    Rewrite.InsertTextBefore(returnStmt->getBeginLoc(),"{compiler2=compiler_;compiler_ = compiler1;");
    /*if(sm.getFileOffset(returnStmt->getBeginLoc()) == sm.getFileOffset(returnStmt->getEndLoc())){
      Rewrite.InsertTextAfter(returnStmt->getEndLoc().getLocWithOffset(7), "}");
      llvm::outs()<<"the offsets are same"<<"\n";
    }
    else Rewrite.InsertTextAfter(returnStmt->getEndLoc().getLocWithOffset(1),";}");*/
    Rewrite.overwriteChangedFiles();
  }
private:
  Rewriter Rewrite;
};
class FunctionDeclHandler : public MatchFinder::MatchCallback{
public:
  FunctionDeclHandler(Rewriter &R): Rewrite(R) {}
  virtual void run(const MatchFinder::MatchResult &Result) {
    const FunctionDecl * fdecl = Result.Nodes.getNodeAs<FunctionDecl>("fd");
    if(!fdecl->hasBody()) return;
    listofallfdecls.insert(trim(fdecl->getNameInfo().getName().getAsString()));
  }
private:
  Rewriter Rewrite;
};
class CallExprHandler : public MatchFinder::MatchCallback {
public:
  CallExprHandler(Rewriter &R) : Rewrite(R){}
  virtual void run(const MatchFinder::MatchResult &Result) {
    const CallExpr * call = Result.Nodes.getNodeAs<CallExpr>("renamecall");
    const FunctionDecl * fcaller = Result.Nodes.getNodeAs<FunctionDecl>("renamecall_caller");
    //f_name_label_parent_label[trim(fcaller->getNameInfo().getName().getAsString())]["function"].insert(make_pair("function", "function"));
    //fname_id[trim(fcaller->getNameInfo().getName().getAsString())] = functionDecl->getID(); // modify call expr works on this part only.
    const SourceManager &sm = Result.Context->getSourceManager();
    const FunctionDecl * fdecl = call->getDirectCallee();
    string called = trim(fdecl->getNameInfo().getName().getAsString());
    // if called is not defined at this location, then it is a reference to some external function.
    //if(sm.getFileOffset(call->getBeginLoc())<f_name_label_offset[trim(fcaller->getNameInfo().getName().getAsString())][called]) return;

    if(!labeldeclsinmainfile[called]) return;   // the called may be some function already defined. No need to rename any callexprs
    const LabelStmt * parentLabel = Result.Nodes.getNodeAs<LabelStmt>("labelStmt");
    // may or may not be valid.
    bool br = 0;
    string parentofcallexpr = "function";
    string caller = "function"; // also the parent.
    bool renamed = false;

    if(!parentLabel) {
      for(auto a : f_name_label_parent_label[trim(fcaller->getNameInfo().getName().getAsString())]) {
        if(a.second == "function" && a.first == called) {
          callablelabels[trim(fcaller->getNameInfo().getName().getAsString())][called] = 1;
          if(sm.getFileOffset(call->getBeginLoc())<f_name_label_offset[trim(fcaller->getNameInfo().getName().getAsString())][called]) break;
          Rewrite.InsertTextAfter(call->getBeginLoc().getLocWithOffset(trim(fdecl->getNameInfo().getName().getAsString()).length()),to_string(fname_id[trim(fcaller->getNameInfo().getName().getAsString())]));
          renamed = true;
          br = 1;
          break;
        }
      }
    }
    else {
      caller = trim(parentLabel->getDecl()->getNameAsString());
      parentofcallexpr = caller;
    }
    // test for other cases of rename
    // Case 1
    if(!renamed) {
      llvm::outs()<<"testing for case 1"<<"\n";
      // hopefully , the caller is assigned a labelname. Otherwise, it'd been handled by the previous case of function decl.
      //handling case 1
      for(auto a : f_name_label_parent_label[trim(fcaller->getNameInfo().getName().getAsString())]) {
        if(a.first == called && a.second == caller) {
          // node accessing itself or one of its children.
          callablelabels[trim(fcaller->getNameInfo().getName().getAsString())][called] = 1;
          if(sm.getFileOffset(call->getBeginLoc())<f_name_label_offset[ trim(fcaller->getNameInfo().getName().getAsString())][called]) break;
          Rewrite.InsertTextAfter(call->getBeginLoc().getLocWithOffset(trim(fdecl->getNameInfo().getName().getAsString()).length()),to_string(fname_id[trim(fcaller->getNameInfo().getName().getAsString())]));
          renamed = true;
          break;
        }
      }
    }
    // case 2:
    if(!renamed){
      llvm::outs()<<"testing for case 2"<<"\n";
      // siblings access each other
      // if called and caller have same parent, then our work is done.
      //first, find out the parent of caller. The caller is the parent of the callexpr - not the parent of the label corresponding to the callexpr
      string parent_caller = "";
      for(auto a : f_name_label_parent_label[trim(fcaller->getNameInfo().getName().getAsString())]) {
        if(a.first == caller) {
          parent_caller = a.second; break;
        }
      }
      if(parent_caller.length()>0) {
        // now test if the parent of called and the parent_caller are same or not.
        for(auto a : f_name_label_parent_label[trim(fcaller->getNameInfo().getName().getAsString())]) {
          if(a.first == called && a.second == parent_caller) {
            renamed = true;
            callablelabels[trim(fcaller->getNameInfo().getName().getAsString())][called] = 1;
            if(sm.getFileOffset(call->getBeginLoc())<f_name_label_offset[trim(fcaller->getNameInfo().getName().getAsString())][called]) break;
            Rewrite.InsertTextAfter(call->getBeginLoc().getLocWithOffset(trim(fdecl->getNameInfo().getName().getAsString()).length()),to_string(fname_id[trim(fcaller->getNameInfo().getName().getAsString())]));
            break;
          }
        }
      }
    }
    // Case 3:
    if(!renamed) {
      llvm::outs()<<"testing for case 3"<<"\n";
      while(caller !="function" && !renamed) {
        llvm::outs()<<"caller is "<<caller<<"\n";
        for (auto a : f_name_label_parent_label[trim(fcaller->getNameInfo().getName().getAsString())]) {
          if(a.first == caller) {
            if(a.second == called) {
              // found. rename and rewrite.
              callablelabels[trim(fcaller->getNameInfo().getName().getAsString())][called] = 1;
              if(sm.getFileOffset(call->getBeginLoc())<f_name_label_offset[trim(fcaller->getNameInfo().getName().getAsString())][called]) break;
              Rewrite.InsertTextAfter(call->getBeginLoc().getLocWithOffset(trim(fdecl->getNameInfo().getName().getAsString()).length()),to_string(fname_id[trim(fcaller->getNameInfo().getName().getAsString())]));
              renamed = true;
              break;
            }
            else if(a.second != called) {
              caller = a.second;
            }
          }
        }
      }
    }
    //Rewrite.InsertTextAfter(call->getBeginLoc().getLocWithOffset(trim(fdecl->getNameInfo().getName().getAsString()).length()),to_string(fname_id[trim(fcaller->getNameInfo().getName().getAsString())]));
    //Rewrite.InsertTextAfter(call->getEndLoc(), "this is the end loc");
    Rewrite.overwriteChangedFiles();
  }
private:
  Rewriter Rewrite;
};
class ForStatementHandler : public MatchFinder::MatchCallback{
public:
  virtual void run(const MatchFinder::MatchResult &Result) {
    const DeclStmt * declstmt = Result.Nodes.getNodeAs<DeclStmt>("declstmt");
    const ForStmt * forstmt = Result.Nodes.getNodeAs<ForStmt>("forstmt");

    if(!forstmt) return;
    if(!declstmt) return;
    Rewrite.RemoveText(declstmt->getSourceRange());
    Rewrite.InsertTextBefore(forstmt->getBeginLoc(),getSourceTextt(Result.Context->getSourceManager(),declstmt)+"  ");
    Rewrite.InsertTextAfter(forstmt->getLParenLoc().getLocWithOffset(1), " ; ");
    Rewrite.overwriteChangedFiles();
  }
  ForStatementHandler(Rewriter &Rewrite): Rewrite(Rewrite){}
private:
  Rewriter Rewrite;
};  // removes the decl statement inside this for statement and puts a ; in place of that declaration.
//Will work in cases where there is no declaration inside the for loop.
// Please note that the declStmt can occur only in the first part of the for loop.
// If there is no decl statement inside the for statment, this handler will not be called.

class UpdateStructConsumer : public ASTConsumer{
public:
  UpdateStructConsumer(Rewriter &R):Rewrite(R) {}
  void HandleTranslationUnit(ASTContext &Context) override {
    SourceManager &sm = Context.getSourceManager();
    //Shiva;
    for(auto a : recordDeclsinScope) {
      for(auto b : a.second) {
        string recordtype = b.first.first;
        string recordstring = b.first.second;
        unsigned recordbeginoffset = b.second.first;
        unsigned recordendoffset = b.second.second;
        unsigned scopeid = recordDecl_offset_scopeid[recordbeginoffset];
        std::regex e ("struct +([a-zA-Z_][0-9a-zA-Z_]*)+[ ]*[{]");
        smatch m;
        regex_search(recordstring,m,e);
        recordstring.replace(recordstring.find(m[0].str()),m[0].str().length(),recordtype+"_"+to_string(scopeid)+"{");
        SourceRange range(sm.getComposedLoc(sm.getMainFileID(), recordbeginoffset), sm.getComposedLoc(sm.getMainFileID(),recordendoffset));
        if(range.isValid()) cout<<"the source range is valid"<<endl;
        Rewrite.ReplaceText(range, recordstring+";");
        for(auto fields : Declarations_refereing_struct[recordbeginoffset]) {
          //for(auto d : fields) {
            string declration = fields.first;
            unsigned offsetdeclarationbegin = fields.second.first;
            unsigned offsetdeclarationend = fields.second.second;
            regex variables ("struct +([a-zA-Z_][0-9a-zA-Z_]*)+[ ]*");
            smatch f;
            regex_search(declration,f,variables);
            declration.replace(declration.find(f[0].str()), f[0].str().length(), recordtype+"_"+to_string(scopeid)+" ");
            SourceRange range1(sm.getComposedLoc(sm.getMainFileID(),offsetdeclarationbegin), sm.getComposedLoc(sm.getMainFileID(),offsetdeclarationend));
            if(range1.isValid()) cout<<"range1 is valid"<<endl;
            Rewrite.ReplaceText(range1, declration);
          //}
        }
      }
    }
    Rewrite.overwriteChangedFiles();
  }
private:
  Rewriter Rewrite;
};
class CallExprConsumer : public ASTConsumer{
public:
  CallExprConsumer(Rewriter &R) : Handle(R) {
    Matcher.addMatcher(callExpr(isExpansionInMainFile(), unless(isExpansionInSystemHeader()), hasAncestor(labelStmt(hasAncestor(functionDecl().bind("renamecall_caller"))).bind("labelStmt"))).bind("renamecall"), &Handle);
    Matcher.addMatcher(callExpr(isExpansionInMainFile(), unless(isExpansionInSystemHeader()), unless(hasAncestor(labelStmt())), hasAncestor(functionDecl().bind("renamecall_caller"))).bind("renamecall"), &Handle);
  }
  void HandleTranslationUnit(ASTContext &Context) override{
    Matcher.matchAST(Context);
  }
private:
  Rewriter Rewrite;
  CallExprHandler Handle;
  MatchFinder Matcher;
};
class MyASTConsumer : public ASTConsumer{
public:
  MyASTConsumer(Rewriter &R) :Handleforcall(R) {
    // Add a simple matcher for finding 'if' statements.
    Matcher.addMatcher(functionDecl(isExpansionInMainFile(), unless(isExpansionInSystemHeader())).bind("function"), &Handleforcall);
    Rewrite = R;
  }

  void HandleTranslationUnit(ASTContext &Context) override {
    // Run the matchers when we have the whole TU parsed.
    Matcher.matchAST(Context);
    SourceManager &sm = Context.getSourceManager();
    for(auto a : labeldeclsinmainfile) {
      llvm::outs()<<a.first<<"\n";
    }
    for(auto a : updatecallexpr) {
      Rewrite.ReplaceText(sm.getComposedLoc(sm.getMainFileID(),a.first), a.second.first, a.second.second);
    }
    //Rewrite.overwriteChangedFiles();
  }

private:
  ModifyCallExpr Handleforcall;
  MatchFinder Matcher;
  Rewriter Rewrite;
};
class FASTConsumer : public ASTConsumer {
public:
  FASTConsumer(Rewriter &R) : labelhandler(R) {
	   Matcher.addMatcher(labelStmt(isExpansionInMainFile(), unless(isExpansionInSystemHeader())).bind("labell"), &labelhandler);
  }
  void HandleTranslationUnit(ASTContext &Context) override {
      Matcher.matchAST(Context);
  }
private:
  MatchFinder Matcher;
  GenerateParams_CallExpr labelhandler;
};
class RenameConsumer1 : public ASTConsumer {
public:
  RenameConsumer1(Rewriter &R): Handle(R){
    Rewrite = R;
    Matcher.addMatcher(declRefExpr(isExpansionInMainFile(), unless(isExpansionInSystemHeader())).bind("DeclRefExpr"), &Handle);
  }
  void HandleTranslationUnit(ASTContext &Context) override {
    Matcher.matchAST(Context);
  }
private:
  RenameVars Handle;
  MatchFinder Matcher;
  Rewriter Rewrite;
};
class RenameConsumer2 : public ASTConsumer {
public:
  RenameConsumer2(Rewriter &R):  Handle2(R){
    Rewrite = R;
    Matcher.addMatcher(varDecl(isExpansionInMainFile(), unless(isExpansionInSystemHeader()),hasLocalStorage()).bind("var"), &Handle2);
  }
  void HandleTranslationUnit(ASTContext &Context) override {
    Matcher.matchAST(Context);
    llvm::outs()<<"size of update is "<<update.size()<<"\n";
    SourceManager &sm = Context.getSourceManager();
    for(auto a : update) {
      Rewrite.InsertTextAfter(sm.getComposedLoc(sm.getMainFileID(),a.first), a.second);
    }
    Rewrite.overwriteChangedFiles();
  }
private:
  RenameVars2 Handle2;
  MatchFinder Matcher;
  Rewriter Rewrite;
};
class RenameConsumer3 : public ASTConsumer {
public:
  RenameConsumer3(Rewriter &R) : Handle(R) {
    Matcher.addMatcher(varDecl(isExpansionInMainFile(), unless(isExpansionInSystemHeader()), hasParent(declStmt().bind("declStmt"))).bind("rename3"), &Handle);
    //Matcher.addMatcher(parmVarDecl().bind("rename3_parameter"), &Handle2);
    Rewrite = R;
  }
  void HandleTranslationUnit(ASTContext &Context) override {
    Matcher.matchAST(Context);
    SourceManager &sm = Context.getSourceManager();
    llvm::outs()<<"*************************************************************************************************************************************************************************************printing data about parameters "<<'\n';
    for (auto a : function_decl_params) {
      cout<<a.first<<" :";
      for(auto b : a.second) {
        cout<<b<<" ";
      }
      cout<<endl;
    }
    for(auto a : decls) {
      Rewrite.InsertTextAfter(sm.getComposedLoc(sm.getMainFileID(), a.first).getLocWithOffset(1), a.second);
    }
    Rewrite.overwriteChangedFiles();
  }
private:
  FindParentsOfDecl_rename3 Handle;
  //FindParentsOfDecl Handle2;
  Rewriter Rewrite;
  MatchFinder Matcher;
};
class FunctionParameterConsumer : public ASTConsumer {
public:
  FunctionParameterConsumer(Rewriter &R) : Handle(R) {
    Matcher.addMatcher(compoundStmt(hasParent(functionDecl().bind("parameterF"))).bind("ParameterCompoundStmt"), &Handle);
  }
  void HandleTranslationUnit(ASTContext &Context) override {
    Matcher.matchAST(Context);
  }
private:
  ParameterDeclHandler Handle;
  MatchFinder Matcher;
};
class FunctionDeclStmtConsumer : public ASTConsumer {
public:
  FunctionDeclStmtConsumer(Rewriter &R) : Handle(R) {
    Matcher.addMatcher(functionDecl(hasParent(declStmt().bind("DeclParent")),hasAncestor(functionDecl().bind("Shiva"))).bind("f_decl"), &Handle);
  }
  void HandleTranslationUnit(ASTContext &Context) override {
    Matcher.matchAST(Context);
  }
private:
  FunctionDeclStmtHandler Handle;
  MatchFinder Matcher;
};
class RenameConsumer4 : public ASTConsumer {
public:
  RenameConsumer4(Rewriter &R): Handle(R) {
    Matcher.addMatcher(declRefExpr(isExpansionInMainFile(), unless(isExpansionInSystemHeader())).bind("DeclRefExpr2"), &Handle);
    Matcher.addMatcher(declRefExpr(isExpansionInMainFile(), unless(isExpansionInSystemHeader()),hasAncestor(returnStmt())).bind("returnedvalue"),&Handle);
    Rewrite = R;
  }
  void HandleTranslationUnit(ASTContext &Context) override {
    Matcher.matchAST(Context);
    SourceManager &sm = Context.getSourceManager();
    string end(renamebeforeuse.size()*2, ' ');
    for(auto a : renamebeforeuse) {
      Rewrite.InsertTextBefore(sm.getComposedLoc(sm.getMainFileID(),a.first), a.second);
    }
    Rewrite.overwriteChangedFiles();
  }
private:
  RenameVarUse Handle;
  MatchFinder Matcher;
  Rewriter Rewrite;
};
class UASTConsumer : public ASTConsumer {
public:
  UASTConsumer(Rewriter &R) : labelleafhandle(R) {
	  Matcher.addMatcher(labelStmt(isExpansionInMainFile(), unless(isExpansionInSystemHeader()), hasAncestor(functionDecl().bind("parent_function"))).bind("label_leaf"), &labelleafhandle);
  }
  void HandleTranslationUnit(ASTContext &Context) override {
      Matcher.matchAST(Context);
  }
private:
  MatchFinder Matcher;
  HoistLabels labelleafhandle;
};
/*class FVASTConsumer : public ASTConsumer {
public:
  FVASTConsumer(Rewriter &R) :FindParentsOfDeclr(R) {
     Matcher.addMatcher(varDecl(isExpansionInMainFile(), unless(isExpansionInSystemHeader()),hasLocalStorage()).bind("var"), &FindParentsOfDeclr);
     Rewrite = R;
  }
  void HandleTranslationUnit(ASTContext &Context) override {
      Matcher.matchAST(Context);
      SourceManager &sm = Context.getSourceManager();
      string end(" ");
      for(auto a : decls) {
        Rewrite.InsertTextAfter(sm.getComposedLoc(sm.getMainFileID(),a.first), a.second);
        string ene(a.second.length()*2, ' ');
        end+=ene;
      }
      Rewrite.overwriteChangedFiles();
  }
private:
  MatchFinder Matcher;
  FindParentsOfDecl_rename3 FindParentsOfDeclr;
  Rewriter Rewrite;
};*/
int structsize = 0;
class Structure : public ASTConsumer {
public:
  Structure(Rewriter &R) : StructureHandlerr(R) {
    Matcher.addMatcher(recordDecl(isExpansionInMainFile(), unless(isExpansionInSystemHeader())).bind("struct"),&StructureHandlerr);
    Rewrite = R;
  }
  void HandleTranslationUnit(ASTContext &Context) override {
    Matcher.matchAST(Context);
    SourceManager &sm = Context.getSourceManager();
    for(auto a: structremove1) {
      Rewrite.RemoveText(sm.getComposedLoc(sm.getMainFileID(), a.first).getLocWithOffset(-1), a.second);
    }
    for(auto a : structInsertafter2) {
      Rewrite.InsertTextAfter(sm.getLocForStartOfFile(sm.getMainFileID()), a.second+"\n");
      structsize+=a.second.size();
    }
    Rewrite.overwriteChangedFiles();
  }
private:
  MatchFinder Matcher;
  StructureHandler StructureHandlerr;
  Rewriter Rewrite;
};
class RecursionConsumer1 : public ASTConsumer {
public:
  RecursionConsumer1(Rewriter &R) : Handle(R) {
    Matcher.addMatcher(compoundStmt(isExpansionInMainFile(),unless(isExpansionInSystemHeader()),hasParent(functionDecl().bind("parent_function"))).bind("recursion1"), &Handle);
  }
  void HandleTranslationUnit(ASTContext &Context) override {
    Matcher.matchAST(Context);
  }
private:
  RecursionHandler_1 Handle;
  MatchFinder Matcher;
};
class RecursionConsumer2 : public ASTConsumer {
public:
  RecursionConsumer2(Rewriter &R): Handle(R) {
    Matcher.addMatcher(returnStmt(isExpansionInMainFile(), unless(isExpansionInSystemHeader()), hasAncestor(functionDecl())).bind("recursion2"), &Handle);
  }
  void HandleTranslationUnit(ASTContext &Context) override {
    Matcher.matchAST(Context);
  }
private:
  RecursionHandler_2 Handle;
  MatchFinder Matcher;
};
class MultidimensionalArrayConsumer : public ASTConsumer {
public:
  MultidimensionalArrayConsumer(Rewriter &R) : Handle(R) {
    Matcher.addMatcher(declRefExpr(isExpansionInMainFile(), unless(isExpansionInSystemHeader()), hasAncestor(compoundStmt())).bind("multiarray"), &Handle);
    Rewrite = R;
  }
  void HandleTranslationUnit(ASTContext &Context) override {
    Matcher.matchAST(Context);
    llvm::outs()<<"creating the renaming of arrays\n";
    SourceManager &sm = Context.getSourceManager();
    for (auto a: commentArray) {
      //Rewrite.InsertTextBefore(sm.getComposedLoc(sm.getMainFileID(),a.first), " /*");
      Rewrite.RemoveText(sm.getComposedLoc(sm.getMainFileID(),a.first), a.second - a.first);
    }
    for(auto a:renameArray){
      Rewrite.InsertTextAfter(sm.getComposedLoc(sm.getMainFileID(),a.first),a.second);
    }
    Rewrite.overwriteChangedFiles();
  }
private:
  MatchFinder Matcher;
  MultidimensionalArray Handle;
  Rewriter Rewrite;
};
class ASTConsumerr : public ASTConsumer {
public:
  ASTConsumerr(Rewriter &R)/*: Handle()*/{
    rewrite = R;
  }
  void HandleTranslationUnit(ASTContext &Context) override {
    SourceManager &sm (Context.getSourceManager());

    string function_labels = "";
    for (auto h : function_decls) {
        function_labels+="void "+h+"(); \n";
    }
    //rewrite.InsertTextAfter(sm.getLocForStartOfFile(sm.getMainFileID()),function_labels+'\n');
    //rewrite.overwriteChangedFiles();
    //rewrite.InsertTextAfter(sm.getComposedLoc(sm.getMainFileID(),main_offset),functions);
    rewrite.InsertTextAfter(sm.getLocForStartOfFile(sm.getMainFileID()),function_labels+'\n');
    rewrite.overwriteChangedFiles();
  }
private:
  Rewriter rewrite;
  MatchFinder Matcher;
};
class AST : public ASTConsumer {
public:
  AST(Rewriter &R){rewrite = R;}
  void HandleTranslationUnit(ASTContext &Context) override {
    SourceManager &sm (Context.getSourceManager());
    unordered_map<string, bool> whetherused;
    string struct_body = "struct compiler {";
    for (auto a : non_array_variables_used_in_program) {
      cout<<a.second.first<<" "<<a.second.second<<endl;
      if(!whetherused[a.second.first]) {
        if(std::count(a.second.second.begin(), a.second.second.end(),'[')) {  // handles int (*)[10] types.
          int found = a.second.second.find("(*)",0);
          if(found!=std::string::npos) a.second.second.replace(found, 3, "");
          found = a.second.second.find("[",0);
          int found2 = a.second.second.find("]",0);
          string substrr = a.second.second.substr(found, found2-found);

          istringstream iss(a.second.second);
          std::vector<string>tokens;
          copy(istream_iterator<string>(iss), istream_iterator<string>(), back_inserter(tokens));
          string type = "";
          for(int i = tokens.size()-2;i>=0; i--) {
            type=tokens[i]+" "+type;
          }
          struct_body+=type+" *"+a.second.first+substrr+"];\n";
        }
        else {
          struct_body+=a.second.second+" *"+a.second.first+";\n";
          whetherused[a.second.first] = true;
        }
      }
    }
    for(auto a : array_variables_used_in_program) {
      string type = a.second.second;
      if(type.length() && !whetherused[a.second.first]) {
        whetherused[a.second.first] = true;
        istringstream iss(type);
        std::vector<string>tokens;
        copy(istream_iterator<string>(iss), istream_iterator<string>(), back_inserter(tokens));
        type = "";
        int count = std::count(tokens[tokens.size()-1].begin(), tokens[tokens.size()-1].end(), '*');
        while(count--) type+="*";
        for(int i = tokens.size()-2;i>=0; i--) {
          type=tokens[i]+" "+type;
        }
        int c = 0;
        struct_body+=type+" *"+a.second.first+";\n";
      }
    }
    rewrite.InsertTextAfter(sm.getLocForStartOfFile(sm.getMainFileID()), struct_body+"}compiler_, compiler1, compiler2;\n");
    string end (struct_body.length()+50, ' ');
    rewrite.overwriteChangedFiles();
  }
private:
  Rewriter rewrite;
};

class FunctionDeclConsumer : public ASTConsumer {
public:
  FunctionDeclConsumer(Rewriter &R):Handle(R){
    Matcher.addMatcher(functionDecl(isExpansionInMainFile(), unless(isExpansionInSystemHeader())).bind("fd"), &Handle);
  }
  void HandleTranslationUnit(ASTContext &Context) override {
    Matcher.matchAST(Context);
  }
private:
  FunctionDeclHandler Handle;
  MatchFinder Matcher;
};
class ForStatementConsumer : public ASTConsumer {
public:
  ForStatementConsumer(Rewriter &R):Handle(R){
    Matcher.addMatcher(declStmt(isExpansionInMainFile(), unless(isExpansionInSystemHeader()),hasAncestor(forStmt().bind("forstmt"))).bind("declstmt"), &Handle);
  }
  void HandleTranslationUnit(ASTContext &Context) override {
    Matcher.matchAST(Context);
    for(auto a: listofallfdecls) {
      llvm::outs()<<a<<" \n";
    }
  }
private:
  int structsize = 0;
  ForStatementHandler Handle;
  MatchFinder Matcher;
};  // handles the declarations inside a for loop.
class RecordDecl1Consumer : public ASTConsumer {
public:
  RecordDecl1Consumer(Rewriter &R): Handle(R) {
    Matcher.addMatcher(recordDecl(isExpansionInMainFile(), unless(isExpansionInSystemHeader()), hasParent(declStmt().bind("enclosingDeclStmt")), hasAncestor(compoundStmt().bind("scope"))).bind("recordecl"), &Handle);
  }
  void HandleTranslationUnit(ASTContext &Context) override {
    Matcher.matchAST(Context);
    for(auto a : scope_record_type) {
      cout<<a.first<<" :";
      for(auto b : a.second) {
        cout<<b.first<<" :: "<<b.second<<" ";
      }
      cout<<endl;
    }
  }
private:
  RecordDecl1 Handle;
  MatchFinder Matcher;
};  // creates scope information for each recordDecl
class RecordDecl2Consumer : public ASTConsumer {
public:
  RecordDecl2Consumer(Rewriter &R): Handle(R),Handle2(R){
    Matcher.addMatcher(fieldDecl(isExpansionInMainFile(), unless(isExpansionInSystemHeader()), hasAncestor(compoundStmt().bind("scope"))).bind("field"), &Handle);
    Matcher.addMatcher(varDecl(isExpansionInMainFile(), unless(isExpansionInSystemHeader()), hasParent(declStmt().bind("declStmt")),hasAncestor(compoundStmt().bind("scope"))).bind("vardecl"), &Handle2);
  }
  void HandleTranslationUnit(ASTContext &Context) override {
    Matcher.matchAST(Context);
  }
private:
  RecordDecl2 Handle;
  RecordDecl3 Handle2;
  MatchFinder Matcher;
};  // creates scope information for each fieldDecl
class RecordDecl3Consumer : public ASTConsumer {
public:
  RecordDecl3Consumer(Rewriter &R): Handle(R) {
    Rewrite = R;
    Matcher.addMatcher(recordDecl(isExpansionInMainFile(), unless(isExpansionInSystemHeader()), hasAncestor(functionDecl().bind("parentfunction")), hasParent(declStmt().bind("declStmt"))).bind("recordDecl"), &Handle);
  }
  void HandleTranslationUnit(ASTContext &Context) override {
    Matcher.matchAST(Context);
  }
private:
  MatchFinder Matcher;
  Rewriter Rewrite;
  RecordDeclHandler Handle;
};

class RenameCallExprAction : public ASTFrontendAction {
public:
  RenameCallExprAction() {}
  /*void EndSourceFileAction() override {
    Rewrite.getEditBuffer(Rewrite.getSourceMgr().getMainFileID()).write(llvm::outs());
  }*/
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<MyASTConsumer>(Rewrite);
  }

private:
  Rewriter Rewrite;
};
class RecordRemovalAction : public ASTFrontendAction {
public:
  RecordRemovalAction(){}
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<RecordDecl3Consumer>(Rewrite);
  }
private:
  Rewriter Rewrite;
};
class ParamsAndCallExprAction : public ASTFrontendAction {
public:
  ParamsAndCallExprAction(){}
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<FASTConsumer>(Rewrite);
  }
private:
  Rewriter Rewrite;
};
class HoistLabelsAction: public ASTFrontendAction {
  public:
    HoistLabelsAction(){}
    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
      Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
      return llvm::make_unique<UASTConsumer>(Rewrite);
    }
  private:
    Rewriter Rewrite;
};
class FunctionsAction : public ASTFrontendAction {
public:
  FunctionsAction(){}
  std::unique_ptr<ASTConsumer>CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<ASTConsumerr>(Rewrite);
  }
private:
  Rewriter Rewrite;
};
class Shiv : public ASTFrontendAction {
public:
  Shiv(){}
  std::unique_ptr<ASTConsumer>CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<AST>(Rewrite);
  }
private:
  Rewriter Rewrite;
};

class RenameVarsAction1 : public ASTFrontendAction {
public:
  RenameVarsAction1() {}
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<RenameConsumer1>(Rewrite);
  }
private:
  Rewriter Rewrite;
};
class RenameVarsAction2 : public ASTFrontendAction {
public:
  RenameVarsAction2() {}
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<RenameConsumer2>(Rewrite);
  }
private:
  Rewriter Rewrite;
};
class RenameVarsAction3 : public ASTFrontendAction {
public:
  RenameVarsAction3() {}
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<RenameConsumer3>(Rewrite);
  }
private:
  Rewriter Rewrite;
};
class FunctionDeclarationAction : public ASTFrontendAction {
public:
  FunctionDeclarationAction() {}
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<FunctionParameterConsumer>(Rewrite);
  }
private:
  Rewriter Rewrite;
};  // creates assignment statements for parameters.  Not required. The parameters assignment is taken care of by the RecursionAction1.
class FunctionDeclStmtAction : public ASTFrontendAction {
public:
  FunctionDeclStmtAction() {}
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<FunctionDeclStmtConsumer>(Rewrite);
  }
private:
  Rewriter Rewrite;
};  // removes function declaration statements and put then on top of enclosing functions
class RenameVarsAction4 : public ASTFrontendAction {
public:
  RenameVarsAction4() {}
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<RenameConsumer4>(Rewrite);
  }

private:
  Rewriter Rewrite;
};
class StructureAction : public ASTFrontendAction {
public:
  StructureAction(){}
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<Structure>(Rewrite);
  }
private:
  Rewriter Rewrite;
};
class RecursionAction1 : public ASTFrontendAction {
public:
  RecursionAction1(){}
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<RecursionConsumer1>(Rewrite);
  }
private:
  Rewriter Rewrite;
};
class RecursionAction2 : public ASTFrontendAction {
public:
  RecursionAction2(){}
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<RecursionConsumer2>(Rewrite);
  }
private:
  Rewriter Rewrite;
};
class MultidimensionalAction : public ASTFrontendAction{
public:
  MultidimensionalAction() {}
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<MultidimensionalArrayConsumer>(Rewrite);
  }
private:
  Rewriter Rewrite;
};
class FunctionDeclAction : public ASTFrontendAction {
public:
  FunctionDeclAction(){}
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<FunctionDeclConsumer>(Rewrite);
  }
private:
  Rewriter Rewrite;
};
class CallExprAAction : public ASTFrontendAction {
public:
  CallExprAAction(){}
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<CallExprConsumer>(Rewrite);
  }
private:
  Rewriter Rewrite;
};
class ForStatementAction : public ASTFrontendAction {
public:
  ForStatementAction(){}
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<ForStatementConsumer>(Rewrite);
  }
private:
  Rewriter Rewrite;
};
class RecordDecl1Action : public ASTFrontendAction {
public:
  RecordDecl1Action(){}
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<RecordDecl1Consumer>(Rewrite);
  }
private:
  Rewriter Rewrite;
};
class RecordDecl2Action : public ASTFrontendAction {
public:
  RecordDecl2Action(){}
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<RecordDecl2Consumer>(Rewrite);
  }
private:
  Rewriter Rewrite;
};
class UpdateStructAction : public ASTFrontendAction {
public:
  UpdateStructAction(){}
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI, StringRef file) override {
    Rewrite.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<UpdateStructConsumer>(Rewrite);
  }
private:
  Rewriter Rewrite;
};

int main(int argc, const char **argv) {
  const char * filename = argv[1];

  std::ifstream in(filename);
  std::stringstream buffer;
  buffer << in.rdbuf();
  string filecontent = buffer.str();
  in.close();

  ofstream myfile;    // replace # include with // #include
  size_t index = 0;
  while(true) {
    // erase all one line comments.
    unsigned index1 = filecontent.find("//", index);
    if(index1 == std::string::npos || index1<0 || index1>filecontent.length()) break;
    unsigned index2 = filecontent.find('\n', index1);
    if(index2 == std::string::npos || index2<0 || index2>filecontent.length()) break;
    filecontent.erase(filecontent.begin()+index1, filecontent.begin()+index2);
    index = 0;
  }
  index = 0;
  while (true) {
     index = filecontent.find("#include", index);
     if (index == std::string::npos || index<0 || index>filecontent.length()) break;
     filecontent.replace(index, 8, "//#include");
     index += 5;
   }
   index = 0;
   while(true) {
     // erase all /**/ comments.
     unsigned index1 = filecontent.find("/*", index);
     if(index1 == std::string::npos || index1<0 || index1>filecontent.length()) break;
     unsigned index2 = filecontent.find("*/", index1);
     if(index2 == std::string::npos || index2<0 || index2>filecontent.length()) break;
     filecontent.erase(filecontent.begin()+index1, filecontent.begin()+index2+2);
     index = index1/2;
   }

   myfile.open(filename, ios::out) ;
   if(myfile.is_open()) {
     myfile<<filecontent<<endl;     // was not able to detect printf. Hence no need to comment it out.
   }
   myfile.close();  // replace done.

    ifstream file;  // appending extra space at the end of the file.
    file.open(filename, std::ifstream::ate | std::ifstream::binary);
    file.seekg(0, ios::end);
    int size = file.tellg();
    file.close();

    ofstream myfile2;
    myfile2.open(filename, ios::app) ;
    if(myfile2.is_open()) {
      string append = "                                \n";
      size /=11;
      myfile2<<"#define EOF (-1)\n";
      myfile2<<"#define NULL (0)\n";
      while(size--)
      myfile2 << append <<endl;
      myfile2<<"/**/"<<endl;
      myfile2.close();
    }

  CommonOptionsParser op(argc, argv, MatcherSampleCategory);
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());
  Tool.run(newFrontendActionFactory<FunctionDeclStmtAction>().get()); // removes the function decls inside a function body.
  Tool.run(newFrontendActionFactory<RecordDecl1Action>().get());
  cout<<"record decl1 action done"<<endl;
  Tool.run(newFrontendActionFactory<RecordDecl2Action>().get());
  cout<<"record decl2 action done "<<endl;
  Tool.run(newFrontendActionFactory<UpdateStructAction>().get());
  cout<<"update action done "<<endl;
  cout<<" ******************************************************** ******************************************* FunctionDeclStmtAction CALLED ************************"<<endl;
  Tool.run(newFrontendActionFactory<RenameVarsAction1>().get()); // renames all the variables as unique inside a label block;
  Tool.run(newFrontendActionFactory<RenameVarsAction2>().get());
  Tool.run(newFrontendActionFactory<Shiv>().get());
  cout<<"structure declared"<<endl;

  Tool.run(newFrontendActionFactory<MultidimensionalAction>().get());
  Tool.run(newFrontendActionFactory<RecordRemovalAction>().get());
  Tool.run(newFrontendActionFactory<RenameVarsAction4>().get());  // need to test for it.
  //Tool.run(newFrontendActionFactory<ForStatementAction>().get()); // check for it. Fits here. Replaces the declaration with a ;
  Tool.run(newFrontendActionFactory<RenameVarsAction3>().get());  // works
  //cout<<"function declaration action done "<<endl;
  std::ifstream in2(filename);
  std::stringstream buffer2;
  buffer2 << in2.rdbuf();
  string filecontent2 = buffer2.str();
  in2.close();

  index = 0;  // replacing back //#include to #include
  while (true) {
     index = filecontent2.find("//#include", index);
     if (index == std::string::npos || index<0 || index>filecontent2.length()) break;
     filecontent2.replace(index, 10, "#include");
     index += 5;
   }

   myfile.open(filename, ios::out) ;
   if(myfile.is_open()) {
     myfile<<filecontent2<<endl;
   }
   myfile.close();

  Tool.run(newFrontendActionFactory<ParamsAndCallExprAction>().get());  // generates label tree and max_depth value.
  cout<<"param called"<<endl;
  Tool.run(newFrontendActionFactory<RenameCallExprAction>().get());
  cout<<"renamecall called"<<endl;
  Tool.run(newFrontendActionFactory<CallExprAAction>().get());  //works
  cout<<"callexpr called"<<endl;

  //max_depth/=2;
  max_depth*=2;
  while(max_depth--)
  Tool.run(newFrontendActionFactory<HoistLabelsAction>().get());  // works
  cout<<"hoist called"<<endl;

  Tool.run(newFrontendActionFactory<FunctionsAction>().get());  // works
  cout<<"Shiva called"<<endl;

  Tool.run(newFrontendActionFactory<FunctionDeclAction>().get()); // in support of recursion handlers.
  cout<<"fdecl called"<<endl;

  Tool.run(newFrontendActionFactory<RecursionAction1>().get()); // works
  cout<<"rec1 called"<<endl;

  Tool.run(newFrontendActionFactory<RecursionAction2>().get()); //works
  cout<<"recl2 called"<<endl;

  std::ifstream in_rec2(filename);
  std::stringstream buffer_rec2;
  buffer_rec2 << in_rec2.rdbuf();
  string filecontent22;
  filecontent22 = buffer_rec2.str();
  cout<<"********************///////////////////////// FILE IS ////////////////////********************\n";
  cout<<filecontent22<<endl;

  in_rec2.close();
  index = 0;
  while (true) {
     index = filecontent22.find("return", index);
     if (index == std::string::npos || index<0 || index>filecontent22.length()) break;
     index = filecontent22.find(";", index);
     if(index == std::string::npos || index<0 || index>filecontent22.length()) break;
     filecontent22.replace(index, 1,";}");
     index+=1;
     //filecontent.replace(index, 8, "//#include");
     //index += 5;
   }
   myfile.open(filename, ios::out) ;
   if(myfile.is_open()) {
     myfile<<filecontent22<<endl;
   }
   myfile.close();
  return 0;
}
