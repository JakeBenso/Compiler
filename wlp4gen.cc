
#include <string>
#include <iostream>
#include <set>
#include <sstream>
#include <stack>
#include <vector>
#include <map>

using namespace std;
string term[35] = {"BOF", "BECOMES", "COMMA", "ELSE", "EOF", "EQ", "GE", "GT", "ID", "IF", "INT", "LBRACE", "LE", "LPAREN", "LT", "MINUS", "NE", "NUM", "PCT", "PLUS", "PRINTLN", "RBRACE", "RETURN", "RPAREN", "SEMI", "SLASH", "STAR", "WAIN", "WHILE", "AMP", "LBRACK", "RBRACK", "NEW", "DELETE", "NULL"};
set<string>terminal;
map<string, pair<string,int> >symbol;
string err;
map<string, map<string, pair<string,int> > >symbol_table;
map<string, vector<string> >id_table;
map<string, string > signature;
map<string, int > paramlist;
map<string,int>total_prod;
string currentproc;
int offset = 0;
string currentid = "";
int Y = -1;
int X = 0;
string type;

struct Tree {
    string rule;
    vector<string>token;
    vector<Tree*> children;
    int length;
    ~Tree() {
        for(vector<Tree*>::iterator it=children.begin(); it != children.end(); it++) {  // delete all subtrees
            delete (*it);
        }
    }
};


void readay(){
    for (int i = 0; i < 35; i++) {
        terminal.insert(term[i]);
    }
}

void BuildTree(Tree *t){
    int len = 0;
    string f; //rule
    getline(cin, f);
    t->rule = f;
    istringstream iss(f);
    string tmp;
    while (iss >> tmp) {
        t->token.push_back(tmp);
        len++;
    }
    t->length = len; // size of children.
    if(terminal.count(t->token[0]) == 0) { // no term
        for (vector<string>::iterator it = t->token.begin()+1; it != t->token.end(); it++) {
            Tree *n = new Tree();   // initionalize a tree
            BuildTree(n);
            t->children.push_back(n);
        }
    }
}

void Build_sym(Tree *t) {
    string type;
    for(int i = 0; i < t->children.size(); i++) {
        if(t->children[i]->token[0] == "main"){
            currentproc = "wain";
            symbol.clear();
            if (total_prod.count(currentproc) == 1) {
                err = "ERROR at duplicate prodecure at " + currentproc;
                throw err;
            }
            else{
                total_prod[currentproc] = 1;
            }
            offset = 0; // reset offset.  assignment 10 action.
            signature["wain"]="wain";
            for (int j = 0; j < t->children[i]->children.size(); j++) {
                if (t->children[i]->children[j]->token[0] == "dcl"){
                    string tmp =signature["wain"];
                    string element = t->children[i]->children[j]->children[1]->token[1];
                    
                    if(t->children[i]->children[j]->children[0]->length == 3){
                        type = " int*";
                        tmp = tmp+type;
                        signature["wain"]=tmp;
                    }
                    else{
                        type = " int";
                        tmp = tmp+type;
                        signature["wain"]=tmp;
                    }
                }
            }
            paramlist["wain"] = 2;
            symbol_table[currentproc] =symbol;
        }
        else if(t->children[i]->rule == "procedure INT ID LPAREN params RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE"){
            currentproc = t->children[i]->children[1]->token[1];
            symbol.clear();
            string tmp = currentproc;
            offset = 0; // reset offset.  assignment 10 action.
            if (total_prod.count(currentproc) == 1) {
                err = "ERROR at duplicate prodecure at *****" + currentproc;
                throw err;
            }
            else{
                total_prod[currentproc] = 1;
            }
            signature[currentproc] = tmp;
            int sum_param = 0;
            if(t->children[i]->children[3]->rule == "params paramlist"){
                Tree *params = t->children[i]->children[3]->children[0];
                // loop the parameter list.
                while (params->children.size() >= 1) { // not  paramslist dcl
                    string element = params->children[0]->children[1]->token[1];
                    sum_param++;
                    if(params->children[0]->children[0]->length == 2){// type of int
                        type = " int";
                        tmp = tmp + type;
                        signature[currentproc] = tmp;
                    }
                    else{
                        type = " int*";
                        tmp = tmp + type;
                        signature[currentproc] = tmp;
                    }
                    // whether the params does not have list.
                    if (params->children.size() == 1) {
                        break;
                    }
                    else{
                    params = params->children[2];
                    }
                }
            }// while loop end
            paramlist[currentproc] = sum_param;
            symbol_table[currentproc] = symbol;
        }
        // push the variable into symboltable if it is not duplicate .
        else if (t->children[i]->token[0] == "dcl"){
            if(t->children[i]->children[0]->children.size() == 2){
                type = " int*";
            }
            else{
                type = " int";
            }
            string tmp =t->children[i]->children[1]->token[1];
            map<string, pair<string,int> >::iterator it;
            it = symbol_table[currentproc].find(tmp);
            if (it == symbol_table[currentproc].end()) { // not find
                symbol[tmp] = make_pair(type,offset);
                offset= offset-4;
                symbol_table[currentproc] =symbol;
            }
            else{
                err = "ERROR at wain, duplicate declar variable " + tmp;
                throw err;
            }
        }
        //   find the id which we used in the scop is valid
        if (t->children[i]->rule == "factor ID" || t->children[i]->rule== "lvalue ID" ){ // check if id is decleared.
            string ID = t->children[i]->children[0]->token[1];
            map<string, pair<string,int> >::iterator it;
            it = symbol_table[currentproc].find(ID);
            if (it == symbol_table[currentproc].end()) {
                err = "ERROR at not declare symbol " + ID;
                throw err;
            }
        }
        // check the procedure is not declar dupilicate or not declear.
        // and the name of procedure which we need to use is not a varible name in the same scop
        if( t->children[i]->token[0] == "factor" && t->children[i]->token[1] == "ID" && t->children[i]->length >=3){ // check if pro decleared
            string pro = t->children[i]->children[0]->token[1]; // get the name of the pro
            if (symbol_table[currentproc].count(pro) == 1){
                err = " ERROR at   " + pro +" sholud be a variable, not a function";
                throw err;
            }
            if (total_prod.count(pro) == 0) {
                err =" ERROR at not declear the procudure " + pro;
                throw err;
            }
            if (symbol_table.count(pro) == 0) {
                err =" ERROR at not declear the procudure " + pro;
                throw err;
            }
        }
        Build_sym(t->children[i]);
    }
}

void printsymbol(){
    for (map< string, map<string, pair<string,int> > >::iterator it = symbol_table.begin(); it != symbol_table.end(); it++) {
        
        if (it->first != "wain") {
            cerr << signature[it->first]  << endl;
            for (map<string,pair<string,int> >::iterator it2 = it->second.begin(); it2 != it->second.end(); it2++) {
                cerr << it2->first << it2->second.first << endl;
            }
                cerr << endl;
        }
    }
    cerr << signature["wain"]  << endl;
    for (map<string,pair<string,int> >::iterator it2 = symbol_table["wain"].begin(); it2 !=symbol_table["wain"].end(); it2++) {
        cerr << it2->first << it2->second.first << endl;
    }
}


string returntype(Tree *t){
    string type;
    // check the dcl and dcls
    if (t->rule == "dcl type ID") {
        type = symbol_table[currentproc][t->children[1]->token[1]].first;
    }
    else if (t->rule == "dcls"){
        type = "valid";  // means valid type
    }
    else if (t->rule == "dcls dcls dcl BECOMES NUM SEMI"){
        if (returntype(t->children[1]) == " int") {
            type = "valid";
        }
        else{
            err = " ERROR at  right of the dcl should be int ";
            throw  err;
        }
    }
    else if (t->rule == "dcls dcls dcl BECOMES NULL SEMI"){
        if (returntype(t->children[1]) == " int*" ) {
            type = "valid";
        }
        else{
            err = " ERROR at  right of the dcl should be int* ";
            throw  err;
        }
    }
    // statements
    else if (t->rule == "statements"){
        type = "valid";
    }
    else if (t->rule == "statements statements statement"){
        if (returntype(t->children[1]) == "valid") {
            type = "valid";
        }
        else{
            err = " ERROR at  the statements statement one of them is error ";
            throw  err;
        }
    }
    else if (t->rule == "statement lvalue BECOMES expr SEMI"){
        if (returntype(t->children[0]) == returntype(t->children[2])) {
            type = "valid";
        }
        else{
            err = " ERROR at lvalue type is not equal to the expr ";
            throw err;
        }
    }
    else if (t->rule == "statement IF LPAREN test RPAREN LBRACE statements RBRACE ELSE LBRACE statements RBRACE"){
        if (returntype(t->children[2]) == "valid" && returntype(t->children[5]) == "valid" && returntype(t->children[9]) == "valid") {
            type = "valid";
        }
        else{
            err = " ERROR at test statements statements which one of them is error ";
            throw  err;
        }
    }
    else if (t->rule == "statement WHILE LPAREN test RPAREN LBRACE statements RBRACE "){
        if (returntype(t->children[2]) == "valid" && returntype(t->children[5]) == "valid") {
            type = "valid";
        }
        else{
            err = " ERROR at test statements which one of them is error ";
            throw  err;
        }
    }
    else if (t->rule == "statement PRINTLN LPAREN expr RPAREN SEMI"){
        if (returntype(t->children[2]) == " int") {
            type = "valid";
        }
        else{
            err = " ERROR at expr which is not int in the println ";
            throw  err;
        }
    }
    else if (t->rule == "statement DELETE LBRACK RBRACK expr SEMI"){
        if (returntype(t->children[3]) == " int*") {
            type = "valid";
        }
        else{
            err = " ERROR at expr which is not int* in the delete ";
            throw  err;
        }
    }
    // test
    else if ((t->rule == "test expr EQ expr") || (t->rule == "test expr NE expr") || (t->rule == "test expr LT expr") || (t->rule == "test expr LE expr") || (t->rule == "test expr GE expr") || (t->rule == "test expr GT expr")){
        if (returntype(t->children[0]) ==  returntype(t->children[2])) { // the type of left expr should equal to type of the right expr
            type = "valid";
        }
        else{
            err = " ERROR at two expr which is error type in the EQ ";
            throw  err;
        }
    }
    // expr
    else if (t->rule == "expr term"){
        type = returntype(t->children[0]);
    }
    else if (t->rule == "expr expr PLUS term"){
        if (returntype(t->children[0]) ==" int" && returntype(t->children[2]) == " int") {
            type = " int";
        }
        else if (returntype(t->children[0]) ==" int*" && returntype(t->children[2]) == " int") {
            type = " int*";
        }
        else if (returntype(t->children[0]) ==" int" && returntype(t->children[2]) == " int*") {
            type = " int*";
        }
        else if (returntype(t->children[0]) ==" int*" && returntype(t->children[2]) == " int*")
        {
            err = " ERROR at first expr is int*, then the second expr cannot be int* in plus+";
            throw  err;
        }
    }
    else if (t->rule == "expr expr MINUS term"){
        if (returntype(t->children[0]) ==" int" && returntype(t->children[2]) == " int") {
            type = " int";
        }
        else if (returntype(t->children[0]) ==" int*" && returntype(t->children[2]) == " int") {
            type = " int*";
        }
        else if (returntype(t->children[0]) ==" int*" && returntype(t->children[2]) == " int*") {
            type = " int";
        }
        else if  (returntype(t->children[0]) ==" int" && returntype(t->children[2]) == " int*"){
            err = " ERROR at first expr is int, then the second expr cannot be int* in miuns-";
            throw  err;
        }
    }
    //term
    else if (t->rule == "term factor"){
        type = returntype(t->children[0]);
    }
    else if ((t->rule == "term term STAR factor") ||(t->rule == "term term SLASH factor") || (t->rule == "term term PCT factor")){
        if( returntype(t->children[0]) == " int" && returntype(t->children[2])==" int"){
            type = " int";
        }
        else{
            err = " ERROR at term and factor one of them or both are not int in star* or slash/ or pct %";
            throw  err;
        }
    }
    // factor
    else if (t->rule == "factor ID" ){
        type = symbol_table[currentproc][t->children[0]->token[1]].first;
    }
    else if (t->rule == "factor NUM"){
        type = " int";
    }
    else if (t->rule == "factor NULL"){
        type = " int*";
    }
    else if (t->rule == "factor LPAREN expr RPAREN"){
        type = returntype(t->children[1]);
    }
    else if (t->rule == "factor AMP lvalue"){
        if (returntype(t->children[1]) == " int") {
            type = " int*";
        }
        else{
            err = " ERROR  at the lvalue is not int after a AMP &";
            throw err;
        }
    }
    else if (t->rule == "factor STAR factor"){
        if (returntype(t->children[1]) == " int*") {
            type = " int";
            
        }
        else{
            err = " ERROR  at the lvalue is not int* after a star *";
            throw err;
        }
    }
    else if (t->rule == "factor NEW INT LBRACK expr RBRACK"){
        if (returntype(t->children[3]) == " int") {
            type = " int*";
        }
        else{
            err = " ERROR  at the expr is not int int a new int";
            throw err;
        }
    }
    else if (t->rule == "factor ID LPAREN RPAREN"){
        string pro = t->children[0]->token[1];
        if (signature[pro] == pro) {
            type = " int";
        }
        else{
            err = " ERROR  at the function " + pro  + " has more than one parameter";
            throw err;
        }
    }
    else if (t->rule == "factor ID LPAREN arglist RPAREN"){
        string pro = t->children[0]->token[1];
        string arguments = pro;
        arguments = arguments + returntype(t->children[2]); // get the rest paramet size and type
        if (signature[pro] == arguments) {
            type = " int";
        }
        else{
            err = " ERROR  in the function " + pro  + " the type of arguments are not the same. ";
            throw err;
        }
    }
    // argulist
    else if(t->rule == "arglist expr"){
        type = returntype(t->children[0]);
    }
    else if(t->rule == "arglist expr COMMA arglist"){
        type = returntype(t->children[0]) + returntype(t->children[2]);
    }
    // lvalue
    else if(t->rule == "lvalue ID"){
        type = symbol_table[currentproc][t->children[0]->token[1]].first;
    }
    else if(t->rule == "lvalue STAR factor"){
        if (returntype(t->children[1]) == " int*") {
            type = " int";
        }
        else{
            err = " ERROR  at factor must be int* before star* in the lvalue";
            throw  err;
        }
    }
    else if(t->rule == "lvalue LPAREN lvalue RPAREN"){
        type = returntype(t->children[1]);
    }
    
    return type;
}

void checktype(Tree *t){
    string type;
    if (t->rule == "main INT WAIN LPAREN dcl COMMA dcl RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE") {
        currentproc = "wain";
        if (returntype(t->children[5]) != " int") {
            err = " ERROR at the second of dcl in wain is not int.";
            throw err;
        }
        if (returntype(t->children[11]) != " int") {
            err = " ERROR at the return type " + currentproc + " is not int";
            throw err;
        }
        
    }
    else if(t->rule == "procedure INT ID LPAREN params RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE"){
        currentproc = t->children[1]->token[1];
        if (returntype(t->children[9]) != " int") {
            err = " ERROR at the return type of " + currentproc + " is not a int";
            throw err;
        }
    }
    else if (t->token[0] == "dcls") {
        type = returntype(t);
    }
    else if (t->token[0] == "expr") {
        type = returntype(t);
    }
    else if (t->token[0] == "statements") {
        type = returntype(t);
    }
    else if (t->token[0] == "test") {
        type = returntype(t);
    }
    else{
        for (int i = 0; i < t->children.size(); i++) {
            checktype(t->children[i]);
        }
    }
}

//************       Assignment 9  ************


void add_sub_slt(string instruction, int d, int s, int t){
    if(instruction == "add"){cout << instruction << " $" << d << ", $" << s << ", $" << t << endl;}
    else if(instruction == "sub"){cout << instruction << " $" << d << ", $" << s << ", $" << t << endl;}
    else  if(instruction == "slt"){cout << instruction << " $" << d << ", $" << s << ", $" << t << endl;}
    else  if(instruction == "sltu"){cout << instruction << " $" << d << ", $" << s << ", $" << t << endl;}
    else{cout << instruction << " $" << d << ", $" << s << ", $" << t << endl;}
}

void mult_div(string instruction, int s, int t){
    if(instruction == "mult"){cout << instruction << " $" << s << ", $" << t << endl;}
    else if(instruction == "multu"){cout << instruction << " $" << s << ", $" << t << endl;}
    else if(instruction == "div"){cout << instruction << " $" << s << ", $" << t << endl;}
    else{cout << instruction << " $" << s << ", $" << t << endl;}
}

void mf_lis_jr(string instruction, int d){
    if (instruction == "mfhi") {cout << instruction << " $" << d << endl;}
    else if (instruction == "mflo") {cout << instruction << " $" << d << endl;}
    else if (instruction == "lis") {cout << instruction << " $" << d << endl;}
    else if (instruction == "jr") {cout << instruction << " $" << d << endl;}
    else if (instruction == "jalr") {cout << instruction << " $" << d << endl;}
}
void dotword(string s){
    cout << ".word " << s << endl;
}
void dotword(int s){
    cout << ".word " << s << endl;
}

void lw_sw(string instruction, int t, int i, int s){
    string action;
    if (instruction == "lw") {action = instruction;}
    else{action = instruction;}
    cout << action << " $" << t << ", " << i << "($"<< s<<")" << endl;
    
}
void beq_bne(string instruction, int s, int t, string i){
    string action;
    if (instruction == "beq") {action = instruction;}
    else{action = instruction;}
    cout << action << " $" << s << ", $" << t << ", "<< i << endl;
}



void prologue(){
    cout << "lis $11" << endl;
    cout << ".word 1" << endl;
    cout << "lis $4" << endl;
    cout << ".word 4" << endl;
    cout <<".import print" << endl;
    cout <<".import init" << endl;
    cout <<".import new" << endl;
    cout <<".import delete" << endl;
    cout << "sub $29, $30, $4" << endl;
    cout << endl;
    
}

void fix(){
    for (map<string, map<string, pair<string,int> > >::iterator it = symbol_table.begin(); it != symbol_table.end(); it++) {
        if (it->first != "wain") {
            int total = paramlist[it->first];
            cerr << total << " paramlist it->second.size()" << endl;
            for (map<string, pair<string,int> >::iterator it2 = it->second.begin(); it2 != it->second.end(); it2++) {
                int tmp = it2->second.second;
                it2->second.second = tmp + total*4;
            }
        }
    }
    
}


void push(int t){
    cout << ";; store register " << t << " in the stack." <<endl;
    lw_sw("sw", t, -4,30);
    add_sub_slt("sub", 30, 30, 4);
}
void pop(int t){
    cout << ";; restore register " << t << " in the stack." <<endl;
    lw_sw("lw", t, 0, 30);
    add_sub_slt("add", 30, 30, 4);
}


void pushstack(int reg, int offset){
    lw_sw("sw", reg, offset, 29);
    add_sub_slt("sub", 30, 30, 4);
}


string countloop(){
    Y++;
    stringstream ss;
    ss << "loop" << Y;
    return ss.str();
}

string lvaluetype(Tree *t){
    string type1 = "";
    if (t->children.size() == 1) {
        type1 = " int";
        return type1;
    }
    else if (t->children.size() == 2){
        type1 = " int*";
        return type1;
    }
    else{
        lvaluetype(t->children[1]);
    }
    return type1;
}


void code(Tree *t){
    if (t->rule == "procedures procedure procedures") {
        code(t->children[1]);
        code(t->children[0]);
    }
    else if (t->rule == "procedures main"){
        code(t->children[0]);
    }
    else if (t->token[0] == "main") {
        cout << "Fwain:" << endl; // A10P5
        currentproc = "wain";
        string id1 = t->children[3]->children[1]->token[1];
        int offset1 = symbol_table[currentproc][id1].second;
        cerr << id1 << " " << offset1 <<endl;
        pushstack(1,offset1);
        string id2 = t->children[5]->children[1]->token[1];
        offset1 = symbol_table[currentproc][id2].second;
        cerr << id2 << " " << offset1 <<endl;
        pushstack(2,offset1);
        cout << endl;
        
        push(31);
        cout << ";; call the init function" << endl;
        if (signature[currentproc] == "wain int* int") {
            mf_lis_jr("lis", 5);
            dotword("init");
            mf_lis_jr("jalr", 5);
        }
        else if (signature[currentproc] == "wain int int"){
            add_sub_slt("add", 2, 0, 0);
            mf_lis_jr("lis", 5);
            dotword("init");
            mf_lis_jr("jalr", 5);
        }
        
        pop(31);
         
        code(t->children[8]);
        code(t->children[9]);
        code(t->children[11]);
        mf_lis_jr("lis", 20);
        dotword("end");
        mf_lis_jr("jr", 20);
        
    }
    else if (t->rule == "procedure INT ID LPAREN params RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE"){
        currentproc = t->children[1]->token[1];
        cout << "F" << currentproc << ":" << endl;
        add_sub_slt("sub", 29, 30, 4);
        code(t->children[6]);// recurse dcls;
        
        push(1);
        push(2);
        push(5);
        push(29);
        push(31);
        code(t->children[7]);
        code(t->children[9]);
        pop(31);
        pop(29);
        pop(5);
        pop(2);
        pop(1);
        add_sub_slt("add", 30, 29, 4);
        mf_lis_jr("jr", 31);
        
    }
    else if (t->rule == "dcls"){
        
    }
    else if (t->rule == "dcls dcls dcl BECOMES NUM SEMI"){
        code(t->children[0]);
        string ss = t->children[1]->children[1]->token[1];
        int offset = symbol_table[currentproc][ss].second;
        mf_lis_jr("lis", 3);
        dotword(t->children[3]->token[1]);
        pushstack(3, offset);
        
    }
    else if (t->rule == "dcls dcls dcl BECOMES NULL SEMI"){
        code(t->children[0]);
        string id = t->children[1]->children[1]->token[1];
        int offset = symbol_table[currentproc][id].second;
        cerr << offset << " offset in the dcl becomes NULL" << endl;
        add_sub_slt("add", 3, 0, 11);
        lw_sw("sw", 3, offset, 29);
        add_sub_slt("sub", 30, 30, 4);
    }
    
    else if (t->rule == "statements"){
    }
    else if(t->rule == "statements statements statement"){
        code(t->children[0]);
        code(t->children[1]);
    }
    
    else if(t->rule == "statement lvalue BECOMES expr SEMI"){
        // lvalue in this rule is only a id
        type = lvaluetype(t->children[0]);
        cerr << type << " the type of " << currentid << " in the  lvalue becomes expr" <<endl ;
        if (type == " int") {
            type = "";
            code(t->children[0]);
            int offset = symbol_table[currentproc][currentid].second;
            code(t->children[2]);
            lw_sw("sw",3, offset, 29);
        }
        else if (type == " int*"){
            type = "";
            code(t->children[2]);
            push(3);
            code(t->children[0]);
            pop(5);
            lw_sw("sw", 5, 0, 3);
        }
    }
    else if (t->rule == "statement IF LPAREN test RPAREN LBRACE statements RBRACE ELSE LBRACE statements RBRACE"){
        code(t->children[2]); // test
        stringstream s_1;
        s_1 << "first" << X;
        string  statement_1 = s_1.str();
        string end = "end" + statement_1;
        beq_bne("beq", 3, 11, statement_1);
        cout << endl;
        X++;
        code(t->children[9]);
        beq_bne("beq", 0, 0, end);
        cout << endl;
        cout << statement_1 << ":" << endl;
        X++;
        code(t->children[5]);
        cout << end << ":" << endl;
    }
    else if (t->rule == "statement WHILE LPAREN test RPAREN LBRACE statements RBRACE"){
        string start = countloop() ;
        string end = "end" + start;
        cout << start <<":"<<endl;
        code(t->children[2]); // call the test
        beq_bne("bne", 11, 3, end);
        code(t->children[5]);
        beq_bne("beq", 0, 0, start);
        cout << endl;
        cout << end <<":" <<  endl;
    }
    else if (t->rule == "statement PRINTLN LPAREN expr RPAREN SEMI"){
        code(t->children[2]);
        push(31);
        cout << ";; call the print function" << endl;
        add_sub_slt("add", 1, 0, 3);
        mf_lis_jr("lis", 5);
        dotword("print");
        mf_lis_jr("jalr", 5);
        pop(31);
        
    }
    else if (t->rule == "statement DELETE LBRACK RBRACK expr SEMI"){
        code(t->children[3]);
        beq_bne("beq", 3, 11, "8");
        push(31);
        cout << ";; call the delete function" << endl;
        add_sub_slt("add", 1, 0, 3);
        mf_lis_jr("lis", 5);
        dotword("delete");
        mf_lis_jr("jalr", 5);
        pop(31);
    }
    else if (t->token[0] == "test"){
        code(t->children[0]);
        push(3);
        code(t->children[2]);
        pop(5);
        string type1 = returntype(t->children[0]);
        if (type1 == " int*") {
            if (t->token[2] == "LT") { // (x < y)
                add_sub_slt("sltu", 3, 5, 3);
            }
            else if (t->token[2] == "GT"){ // x > y
                add_sub_slt("sltu", 3, 3, 5);
            }
            else if (t->token[2] == "EQ"){
                add_sub_slt("sltu", 6, 3, 5);
                add_sub_slt("sltu", 7, 5, 3);
                add_sub_slt("add", 3, 6, 7);
                add_sub_slt("sub", 3, 11, 3);
            }
            else if (t->token[2] == "NE"){
                add_sub_slt("sltu", 6, 3, 5);
                add_sub_slt("sltu", 7, 5, 3);
                add_sub_slt("add", 3, 6, 7);
            }
            else if (t->token[2] == "LE"){// !(x > y)
                add_sub_slt("sltu", 3, 3, 5);
                add_sub_slt("sub", 3, 11, 3); // !
            }
            else if (t->token[2] == "GE"){ // !(X < y)
                add_sub_slt("sltu", 3, 5, 3);
                add_sub_slt("sub", 3, 11, 3);
            }
        }
        else{
            if (t->token[2] == "LT") { // (x < y)
                add_sub_slt("slt", 3, 5, 3);
            }
            else if (t->token[2] == "GT"){ // x > y
                add_sub_slt("slt", 3, 3, 5);
            }
            else if (t->token[2] == "EQ"){
                add_sub_slt("slt", 6, 3, 5);
                add_sub_slt("slt", 7, 5, 3);
                add_sub_slt("add", 3, 6, 7);
                add_sub_slt("sub", 3, 11, 3);
            }
            else if (t->token[2] == "NE"){
                add_sub_slt("slt", 6, 3, 5);
                add_sub_slt("slt", 7, 5, 3);
                add_sub_slt("add", 3, 6, 7);
            }
            else if (t->token[2] == "LE"){// !(x > y)
                add_sub_slt("slt", 3, 3, 5);
                add_sub_slt("sub", 3, 11, 3); // !
            }
            else if (t->token[2] == "GE"){ // !(X < y)
                add_sub_slt("slt", 3, 5, 3);
                add_sub_slt("sub", 3, 11, 3);
            }
        }
    }
    else if (t->rule == "expr term"){
        code(t->children[0]);
    }
    else if (t->token[0] == "expr" && t->token[1] == "expr" && t->children.size() == 3){
        code(t->children[0]);
        push(3);
        code(t->children[2]);
        pop(5);
        string type1 = returntype(t->children[0]);
        string type2 = returntype(t->children[2]);
        if (t->token[2] == "PLUS") {
            if (type1 == " int" && type2 == " int") {
                add_sub_slt("add", 3, 5, 3);
            }
            else if (type1 == " int*" && type2 == " int"){
                mult_div("mult", 3, 4);
                mf_lis_jr("mflo", 3);
                add_sub_slt("add", 3, 5, 3);
            }
            else if (type1 == " int" && type2 == " int*"){
                mult_div("mult", 5, 4);
                mf_lis_jr("mflo", 5);
                add_sub_slt("add", 3, 5, 3);
            }
        }
        else if (t->token[2] == "MINUS"){
            if (type1 == " int" && type2 == " int") {
                add_sub_slt("sub", 3, 5, 3);
            }
            else if (type1 == " int*" && type2 == " int"){
                mult_div("mult", 3, 4);
                mf_lis_jr("mflo", 3);
                add_sub_slt("sub", 3, 5, 3);
            }
            else if (type1 == " int*" && type2 == " int*"){
                add_sub_slt("sub", 3, 5, 3);
                mult_div("div", 3, 4);
                mf_lis_jr("mflo", 3);
            }
        }
    }
    
    else if (t->rule == "term factor"){
        code(t->children[0]);
    }
    else if (t->token[0] == "term" && t->token[1] == "term" && t->children.size() == 3){
        code(t->children[0]);
        push(3);
        code(t->children[2]);
        pop(5);
        if (t->token[2] == "STAR") {
            mult_div("mult", 5, 3);
            mf_lis_jr("mflo", 3);
        }
        else if (t->token[2] == "SLASH"){
            mult_div("div", 5, 3);
            mf_lis_jr("mflo", 3);
        }
        else if(t->token[2] == "PCT"){
            mult_div("div", 5, 3);
            mf_lis_jr("mfhi", 3);
        }
    }
    else if (t->rule == "factor ID"){
        string id = t->children[0]->token[1];
        int off = symbol_table[currentproc][id].second;
        lw_sw("lw", 3, off, 29);
    }
    else if( t->rule == "factor NUM"){
        string number= t->children[0]->token[1];
        mf_lis_jr("lis", 3);
        dotword(number);
    }
    else if (t->rule == "factor NULL"){
        add_sub_slt("add", 3, 0, 11);
    }
    else if (t->rule == "factor LPAREN expr RPAREN"){
        code(t->children[1]);
    }
    else if (t->rule == "factor AMP lvalue"){
        type = "AMP";
        code(t->children[1]);
        
    }
    else if (t->rule == "factor STAR factor"){
        code(t->children[1]);
        lw_sw("lw", 3, 0, 3);
    }
    else if(t->rule == "factor NEW INT LBRACK expr RBRACK"){
        code(t->children[3]);
        push(31);
        cout << ";; call the new function" << endl;
        add_sub_slt("add", 1, 0, 3);
        mf_lis_jr("lis", 5);
        dotword("new");
        mf_lis_jr("jalr", 5);
        beq_bne("bne", 3, 0, "1");
        add_sub_slt("add", 3, 0, 11);
        pop(31);
        
    }
    //&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&
    else if (t->rule == "factor ID LPAREN RPAREN"){
        push(29);
        push(31);
        mf_lis_jr("lis", 5);
        string tmp = "F"+ t->children[0]->token[1];
        dotword(tmp);
        mf_lis_jr("jalr", 5);
        pop(31);
        pop(29);
    }
    else if (t->rule == "factor ID LPAREN arglist RPAREN"){
        
        push(29);
        push(31);
        code(t->children[2]);
        
        string tmp = "F"+ t->children[0]->token[1];
    
        mf_lis_jr("lis", 5);
        dotword(tmp);
        mf_lis_jr("jalr", 5);
        
        int poptime = paramlist[t->children[0]->token[1]] *4;
        mf_lis_jr("lis", 15);
        dotword(poptime);
        add_sub_slt("add", 30, 30, 15);
        pop(31);
        pop(29);
    }
    else if(t->rule =="arglist expr"){
        code(t->children[0]);
        push(3);
    }
    else if(t->rule == "arglist expr COMMA arglist"){
        code(t->children[0]);
        push(3);
        code(t->children[2]);
    }
    else if(t->rule == "lvalue ID"){
        currentid = t->children[0]->token[1];
        cerr << type << "  the type of the " << currentid << " which in the rule lvalue id " << endl;
        if (type == "AMP") {
            mf_lis_jr("lis", 3);
            int offset = symbol_table[currentproc][currentid].second;
            dotword(offset);
            add_sub_slt("add", 3, 29, 3);
            type = "";
        }
        
    }
    else if (t->rule == "lvalue STAR factor"){
        code(t->children[1]);
    }
    else if (t->rule == "lvalue LPAREN lvalue RPAREN"){
        code(t->children[1]);
    }
    else{
        for (int i = 0; i < t->children.size(); i++) {
            code(t->children[i]);
        }
    }
    
}


void end(){
    cout << endl;
    cout << "end: " <<endl;
    cout << ";; put $30 go back to the original position" << endl;
    int moveback = symbol_table["wain"].size()*4;
    mf_lis_jr("lis", 19);
    dotword(moveback);
    add_sub_slt("add", 30, 30, 19);
    
    cout << "jr $31" <<endl;
}

int main(){
    Tree *parsetree = new Tree();
    try {
        readay();
        BuildTree(parsetree);
        Build_sym(parsetree);
        checktype(parsetree);
        
        fix(); // fix the procedure offset.
        printsymbol();
        prologue();  //
        code(parsetree);
        end();
        
   } catch (const string & err) {
      cerr << err << endl;
   }
    delete parsetree;
}
