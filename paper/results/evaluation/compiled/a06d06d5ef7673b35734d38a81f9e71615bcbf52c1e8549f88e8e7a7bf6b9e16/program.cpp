#define SOUFFLE_GENERATOR_VERSION ""
#include "souffle/CompiledSouffle.h"
#include "souffle/SignalHandler.h"
#include "souffle/SouffleInterface.h"
#include "souffle/datastructure/BTree.h"
#include "souffle/io/IOSystem.h"
#include "souffle/utility/MiscUtil.h"
#include <any>
namespace functors {
extern "C" {
}
} //namespace functors
namespace souffle::t_btree_000_ii__0_1__11__10 {
using namespace souffle;
struct Type {
static constexpr Relation::arity_type Arity = 2;
using t_tuple = Tuple<RamDomain, 2>;
struct t_comparator_0{
 int operator()(const t_tuple& a, const t_tuple& b) const {
  return (ramBitCast<RamSigned>(a[0]) < ramBitCast<RamSigned>(b[0])) ? -1 : (ramBitCast<RamSigned>(a[0]) > ramBitCast<RamSigned>(b[0])) ? 1 :((ramBitCast<RamSigned>(a[1]) < ramBitCast<RamSigned>(b[1])) ? -1 : (ramBitCast<RamSigned>(a[1]) > ramBitCast<RamSigned>(b[1])) ? 1 :(0));
 }
bool less(const t_tuple& a, const t_tuple& b) const {
  return (ramBitCast<RamSigned>(a[0]) < ramBitCast<RamSigned>(b[0]))|| ((ramBitCast<RamSigned>(a[0]) == ramBitCast<RamSigned>(b[0])) && ((ramBitCast<RamSigned>(a[1]) < ramBitCast<RamSigned>(b[1]))));
 }
bool equal(const t_tuple& a, const t_tuple& b) const {
return (ramBitCast<RamSigned>(a[0]) == ramBitCast<RamSigned>(b[0]))&&(ramBitCast<RamSigned>(a[1]) == ramBitCast<RamSigned>(b[1]));
 }
};
using t_ind_0 = btree_set<t_tuple,t_comparator_0>;
t_ind_0 ind_0;
using iterator = t_ind_0::iterator;
struct context {
t_ind_0::operation_hints hints_0_lower;
t_ind_0::operation_hints hints_0_upper;
};
context createContext() { return context(); }
bool insert(const t_tuple& t);
bool insert(const t_tuple& t, context& h);
bool insert(const RamDomain* ramDomain);
bool insert(RamDomain a0,RamDomain a1);
bool contains(const t_tuple& t, context& h) const;
bool contains(const t_tuple& t) const;
std::size_t size() const;
iterator find(const t_tuple& t, context& h) const;
iterator find(const t_tuple& t) const;
range<iterator> lowerUpperRange_00(const t_tuple& /* lower */, const t_tuple& /* upper */, context& /* h */) const;
range<iterator> lowerUpperRange_00(const t_tuple& /* lower */, const t_tuple& /* upper */) const;
range<t_ind_0::iterator> lowerUpperRange_11(const t_tuple& lower, const t_tuple& upper, context& h) const;
range<t_ind_0::iterator> lowerUpperRange_11(const t_tuple& lower, const t_tuple& upper) const;
range<t_ind_0::iterator> lowerUpperRange_10(const t_tuple& lower, const t_tuple& upper, context& h) const;
range<t_ind_0::iterator> lowerUpperRange_10(const t_tuple& lower, const t_tuple& upper) const;
bool empty() const;
std::vector<range<iterator>> partition() const;
void purge();
iterator begin() const;
iterator end() const;
void printStatistics(std::ostream& o) const;
};
} // namespace souffle::t_btree_000_ii__0_1__11__10 
namespace souffle::t_btree_000_ii__0_1__11__10 {
using namespace souffle;
using t_ind_0 = Type::t_ind_0;
using iterator = Type::iterator;
using context = Type::context;
bool Type::insert(const t_tuple& t) {
context h;
return insert(t, h);
}
bool Type::insert(const t_tuple& t, context& h) {
if (ind_0.insert(t, h.hints_0_lower)) {
return true;
} else return false;
}
bool Type::insert(const RamDomain* ramDomain) {
RamDomain data[2];
std::copy(ramDomain, ramDomain + 2, data);
const t_tuple& tuple = reinterpret_cast<const t_tuple&>(data);
context h;
return insert(tuple, h);
}
bool Type::insert(RamDomain a0,RamDomain a1) {
RamDomain data[2] = {a0,a1};
return insert(data);
}
bool Type::contains(const t_tuple& t, context& h) const {
return ind_0.contains(t, h.hints_0_lower);
}
bool Type::contains(const t_tuple& t) const {
context h;
return contains(t, h);
}
std::size_t Type::size() const {
return ind_0.size();
}
iterator Type::find(const t_tuple& t, context& h) const {
return ind_0.find(t, h.hints_0_lower);
}
iterator Type::find(const t_tuple& t) const {
context h;
return find(t, h);
}
range<iterator> Type::lowerUpperRange_00(const t_tuple& /* lower */, const t_tuple& /* upper */, context& /* h */) const {
return range<iterator>(ind_0.begin(),ind_0.end());
}
range<iterator> Type::lowerUpperRange_00(const t_tuple& /* lower */, const t_tuple& /* upper */) const {
return range<iterator>(ind_0.begin(),ind_0.end());
}
range<t_ind_0::iterator> Type::lowerUpperRange_11(const t_tuple& lower, const t_tuple& upper, context& h) const {
t_comparator_0 comparator;
int cmp = comparator(lower, upper);
if (cmp == 0) {
    auto pos = ind_0.find(lower, h.hints_0_lower);
    auto fin = ind_0.end();
    if (pos != fin) {fin = pos; ++fin;}
    return make_range(pos, fin);
}
if (cmp > 0) {
    return make_range(ind_0.end(), ind_0.end());
}
return make_range(ind_0.lower_bound(lower, h.hints_0_lower), ind_0.upper_bound(upper, h.hints_0_upper));
}
range<t_ind_0::iterator> Type::lowerUpperRange_11(const t_tuple& lower, const t_tuple& upper) const {
context h;
return lowerUpperRange_11(lower,upper,h);
}
range<t_ind_0::iterator> Type::lowerUpperRange_10(const t_tuple& lower, const t_tuple& upper, context& h) const {
t_comparator_0 comparator;
int cmp = comparator(lower, upper);
if (cmp > 0) {
    return make_range(ind_0.end(), ind_0.end());
}
return make_range(ind_0.lower_bound(lower, h.hints_0_lower), ind_0.upper_bound(upper, h.hints_0_upper));
}
range<t_ind_0::iterator> Type::lowerUpperRange_10(const t_tuple& lower, const t_tuple& upper) const {
context h;
return lowerUpperRange_10(lower,upper,h);
}
bool Type::empty() const {
return ind_0.empty();
}
std::vector<range<iterator>> Type::partition() const {
return ind_0.getChunks(400);
}
void Type::purge() {
ind_0.clear();
}
iterator Type::begin() const {
return ind_0.begin();
}
iterator Type::end() const {
return ind_0.end();
}
void Type::printStatistics(std::ostream& o) const {
o << " arity 2 direct b-tree index 0 lex-order [0,1]\n";
ind_0.printStats(o);
}
} // namespace souffle::t_btree_000_ii__0_1__11__10 
namespace souffle::t_btree_000_i__0__1 {
using namespace souffle;
struct Type {
static constexpr Relation::arity_type Arity = 1;
using t_tuple = Tuple<RamDomain, 1>;
struct t_comparator_0{
 int operator()(const t_tuple& a, const t_tuple& b) const {
  return (ramBitCast<RamSigned>(a[0]) < ramBitCast<RamSigned>(b[0])) ? -1 : (ramBitCast<RamSigned>(a[0]) > ramBitCast<RamSigned>(b[0])) ? 1 :(0);
 }
bool less(const t_tuple& a, const t_tuple& b) const {
  return (ramBitCast<RamSigned>(a[0]) < ramBitCast<RamSigned>(b[0]));
 }
bool equal(const t_tuple& a, const t_tuple& b) const {
return (ramBitCast<RamSigned>(a[0]) == ramBitCast<RamSigned>(b[0]));
 }
};
using t_ind_0 = btree_set<t_tuple,t_comparator_0>;
t_ind_0 ind_0;
using iterator = t_ind_0::iterator;
struct context {
t_ind_0::operation_hints hints_0_lower;
t_ind_0::operation_hints hints_0_upper;
};
context createContext() { return context(); }
bool insert(const t_tuple& t);
bool insert(const t_tuple& t, context& h);
bool insert(const RamDomain* ramDomain);
bool insert(RamDomain a0);
bool contains(const t_tuple& t, context& h) const;
bool contains(const t_tuple& t) const;
std::size_t size() const;
iterator find(const t_tuple& t, context& h) const;
iterator find(const t_tuple& t) const;
range<iterator> lowerUpperRange_0(const t_tuple& /* lower */, const t_tuple& /* upper */, context& /* h */) const;
range<iterator> lowerUpperRange_0(const t_tuple& /* lower */, const t_tuple& /* upper */) const;
range<t_ind_0::iterator> lowerUpperRange_1(const t_tuple& lower, const t_tuple& upper, context& h) const;
range<t_ind_0::iterator> lowerUpperRange_1(const t_tuple& lower, const t_tuple& upper) const;
bool empty() const;
std::vector<range<iterator>> partition() const;
void purge();
iterator begin() const;
iterator end() const;
void printStatistics(std::ostream& o) const;
};
} // namespace souffle::t_btree_000_i__0__1 
namespace souffle::t_btree_000_i__0__1 {
using namespace souffle;
using t_ind_0 = Type::t_ind_0;
using iterator = Type::iterator;
using context = Type::context;
bool Type::insert(const t_tuple& t) {
context h;
return insert(t, h);
}
bool Type::insert(const t_tuple& t, context& h) {
if (ind_0.insert(t, h.hints_0_lower)) {
return true;
} else return false;
}
bool Type::insert(const RamDomain* ramDomain) {
RamDomain data[1];
std::copy(ramDomain, ramDomain + 1, data);
const t_tuple& tuple = reinterpret_cast<const t_tuple&>(data);
context h;
return insert(tuple, h);
}
bool Type::insert(RamDomain a0) {
RamDomain data[1] = {a0};
return insert(data);
}
bool Type::contains(const t_tuple& t, context& h) const {
return ind_0.contains(t, h.hints_0_lower);
}
bool Type::contains(const t_tuple& t) const {
context h;
return contains(t, h);
}
std::size_t Type::size() const {
return ind_0.size();
}
iterator Type::find(const t_tuple& t, context& h) const {
return ind_0.find(t, h.hints_0_lower);
}
iterator Type::find(const t_tuple& t) const {
context h;
return find(t, h);
}
range<iterator> Type::lowerUpperRange_0(const t_tuple& /* lower */, const t_tuple& /* upper */, context& /* h */) const {
return range<iterator>(ind_0.begin(),ind_0.end());
}
range<iterator> Type::lowerUpperRange_0(const t_tuple& /* lower */, const t_tuple& /* upper */) const {
return range<iterator>(ind_0.begin(),ind_0.end());
}
range<t_ind_0::iterator> Type::lowerUpperRange_1(const t_tuple& lower, const t_tuple& upper, context& h) const {
t_comparator_0 comparator;
int cmp = comparator(lower, upper);
if (cmp == 0) {
    auto pos = ind_0.find(lower, h.hints_0_lower);
    auto fin = ind_0.end();
    if (pos != fin) {fin = pos; ++fin;}
    return make_range(pos, fin);
}
if (cmp > 0) {
    return make_range(ind_0.end(), ind_0.end());
}
return make_range(ind_0.lower_bound(lower, h.hints_0_lower), ind_0.upper_bound(upper, h.hints_0_upper));
}
range<t_ind_0::iterator> Type::lowerUpperRange_1(const t_tuple& lower, const t_tuple& upper) const {
context h;
return lowerUpperRange_1(lower,upper,h);
}
bool Type::empty() const {
return ind_0.empty();
}
std::vector<range<iterator>> Type::partition() const {
return ind_0.getChunks(400);
}
void Type::purge() {
ind_0.clear();
}
iterator Type::begin() const {
return ind_0.begin();
}
iterator Type::end() const {
return ind_0.end();
}
void Type::printStatistics(std::ostream& o) const {
o << " arity 1 direct b-tree index 0 lex-order [0]\n";
ind_0.printStats(o);
}
} // namespace souffle::t_btree_000_i__0__1 
namespace  souffle {
using namespace souffle;
class Stratum_answer_6c655231fec607ba {
public:
 Stratum_answer_6c655231fec607ba(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_i__0__1::Type& rel_answer_227ae7ad3b0ead1f,t_btree_000_ii__0_1__11__10::Type& rel_p_earlier_58b11d5a418636a9);
void run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret);
private:
SymbolTable& symTable;
RecordTable& recordTable;
ConcurrentCache<std::string,std::regex>& regexCache;
bool& pruneImdtRels;
bool& performIO;
SignalHandler*& signalHandler;
std::atomic<std::size_t>& iter;
std::atomic<RamDomain>& ctr;
std::string& inputDirectory;
std::string& outputDirectory;
t_btree_000_i__0__1::Type* rel_answer_227ae7ad3b0ead1f;
t_btree_000_ii__0_1__11__10::Type* rel_p_earlier_58b11d5a418636a9;
};
} // namespace  souffle
namespace  souffle {
using namespace souffle;
 Stratum_answer_6c655231fec607ba::Stratum_answer_6c655231fec607ba(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_i__0__1::Type& rel_answer_227ae7ad3b0ead1f,t_btree_000_ii__0_1__11__10::Type& rel_p_earlier_58b11d5a418636a9):
symTable(symTable),
recordTable(recordTable),
regexCache(regexCache),
pruneImdtRels(pruneImdtRels),
performIO(performIO),
signalHandler(signalHandler),
iter(iter),
ctr(ctr),
inputDirectory(inputDirectory),
outputDirectory(outputDirectory),
rel_answer_227ae7ad3b0ead1f(&rel_answer_227ae7ad3b0ead1f),
rel_p_earlier_58b11d5a418636a9(&rel_p_earlier_58b11d5a418636a9){
}

void Stratum_answer_6c655231fec607ba::run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret){
signalHandler->setMsg(R"_(answer(0) :- 
   p_earlier("N12","N15").
in file input.dl [6:1-6:37])_");
if(!(rel_p_earlier_58b11d5a418636a9->empty())) {
[&](){
CREATE_OP_CONTEXT(rel_answer_227ae7ad3b0ead1f_op_ctxt,rel_answer_227ae7ad3b0ead1f->createContext());
CREATE_OP_CONTEXT(rel_p_earlier_58b11d5a418636a9_op_ctxt,rel_p_earlier_58b11d5a418636a9->createContext());
if(rel_p_earlier_58b11d5a418636a9->contains(Tuple<RamDomain,2>{{ramBitCast(RamSigned(0)),ramBitCast(RamSigned(1))}},READ_OP_CONTEXT(rel_p_earlier_58b11d5a418636a9_op_ctxt))) {
Tuple<RamDomain,1> tuple{{ramBitCast(RamSigned(0))}};
rel_answer_227ae7ad3b0ead1f->insert(tuple,READ_OP_CONTEXT(rel_answer_227ae7ad3b0ead1f_op_ctxt));
}
}
();}
if (performIO) {
try {std::map<std::string, std::string> directiveMap({{R"_(IO)_",R"_(file)_"},{R"_(attributeNames)_",R"_(i)_"},{R"_(auxArity)_",R"_(0)_"},{R"_(name)_",R"_(answer)_"},{R"_(operation)_",R"_(output)_"},{R"_(output-dir)_",R"_(.)_"},{R"_(params)_",R"_({"records": {}, "relation": {"arity": 1, "params": ["i"]}})_"},{R"_(types)_",R"_({"ADTs": {}, "records": {}, "relation": {"arity": 1, "types": ["i:number"]}})_"}});
if (outputDirectory == "-"){directiveMap["IO"] = "stdout"; directiveMap["headers"] = "true";}
else if (!outputDirectory.empty()) {directiveMap["output-dir"] = outputDirectory;}
IOSystem::getInstance().getWriter(directiveMap, symTable, recordTable)->writeAll(*rel_answer_227ae7ad3b0ead1f);
} catch (std::exception& e) {std::cerr << e.what();exit(1);}
}
if (pruneImdtRels) rel_p_earlier_58b11d5a418636a9->purge();
}

} // namespace  souffle

namespace  souffle {
using namespace souffle;
class Stratum_p_earlier_3f10fbf7b3477d6b {
public:
 Stratum_p_earlier_3f10fbf7b3477d6b(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_ii__0_1__11__10::Type& rel_delta_p_earlier_a8001e593b7d88d7,t_btree_000_ii__0_1__11__10::Type& rel_new_p_earlier_b29f1557490eb09b,t_btree_000_ii__0_1__11__10::Type& rel_p_earlier_58b11d5a418636a9);
void run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret);
private:
SymbolTable& symTable;
RecordTable& recordTable;
ConcurrentCache<std::string,std::regex>& regexCache;
bool& pruneImdtRels;
bool& performIO;
SignalHandler*& signalHandler;
std::atomic<std::size_t>& iter;
std::atomic<RamDomain>& ctr;
std::string& inputDirectory;
std::string& outputDirectory;
t_btree_000_ii__0_1__11__10::Type* rel_delta_p_earlier_a8001e593b7d88d7;
t_btree_000_ii__0_1__11__10::Type* rel_new_p_earlier_b29f1557490eb09b;
t_btree_000_ii__0_1__11__10::Type* rel_p_earlier_58b11d5a418636a9;
};
} // namespace  souffle
namespace  souffle {
using namespace souffle;
 Stratum_p_earlier_3f10fbf7b3477d6b::Stratum_p_earlier_3f10fbf7b3477d6b(SymbolTable& symTable,RecordTable& recordTable,ConcurrentCache<std::string,std::regex>& regexCache,bool& pruneImdtRels,bool& performIO,SignalHandler*& signalHandler,std::atomic<std::size_t>& iter,std::atomic<RamDomain>& ctr,std::string& inputDirectory,std::string& outputDirectory,t_btree_000_ii__0_1__11__10::Type& rel_delta_p_earlier_a8001e593b7d88d7,t_btree_000_ii__0_1__11__10::Type& rel_new_p_earlier_b29f1557490eb09b,t_btree_000_ii__0_1__11__10::Type& rel_p_earlier_58b11d5a418636a9):
symTable(symTable),
recordTable(recordTable),
regexCache(regexCache),
pruneImdtRels(pruneImdtRels),
performIO(performIO),
signalHandler(signalHandler),
iter(iter),
ctr(ctr),
inputDirectory(inputDirectory),
outputDirectory(outputDirectory),
rel_delta_p_earlier_a8001e593b7d88d7(&rel_delta_p_earlier_a8001e593b7d88d7),
rel_new_p_earlier_b29f1557490eb09b(&rel_new_p_earlier_b29f1557490eb09b),
rel_p_earlier_58b11d5a418636a9(&rel_p_earlier_58b11d5a418636a9){
}

void Stratum_p_earlier_3f10fbf7b3477d6b::run([[maybe_unused]] const std::vector<RamDomain>& args,[[maybe_unused]] std::vector<RamDomain>& ret){
if (performIO) {
try {std::map<std::string, std::string> directiveMap({{R"_(IO)_",R"_(file)_"},{R"_(attributeNames)_",R"_(a0	a1)_"},{R"_(auxArity)_",R"_(0)_"},{R"_(fact-dir)_",R"_(.)_"},{R"_(name)_",R"_(p_earlier)_"},{R"_(operation)_",R"_(input)_"},{R"_(params)_",R"_({"records": {}, "relation": {"arity": 2, "params": ["a0", "a1"]}})_"},{R"_(types)_",R"_({"ADTs": {}, "records": {}, "relation": {"arity": 2, "types": ["s:symbol", "s:symbol"]}})_"}});
if (!inputDirectory.empty()) {directiveMap["fact-dir"] = inputDirectory;}
IOSystem::getInstance().getReader(directiveMap, symTable, recordTable)->readAll(*rel_p_earlier_58b11d5a418636a9);
} catch (std::exception& e) {std::cerr << "Error loading p_earlier data: " << e.what() << '\n';
exit(1);
}
}
[&](){
CREATE_OP_CONTEXT(rel_delta_p_earlier_a8001e593b7d88d7_op_ctxt,rel_delta_p_earlier_a8001e593b7d88d7->createContext());
CREATE_OP_CONTEXT(rel_p_earlier_58b11d5a418636a9_op_ctxt,rel_p_earlier_58b11d5a418636a9->createContext());
for(const auto& env0 : *rel_p_earlier_58b11d5a418636a9) {
Tuple<RamDomain,2> tuple{{ramBitCast(env0[0]),ramBitCast(env0[1])}};
rel_delta_p_earlier_a8001e593b7d88d7->insert(tuple,READ_OP_CONTEXT(rel_delta_p_earlier_a8001e593b7d88d7_op_ctxt));
}
}
();auto loop_counter = RamUnsigned(1);
iter = 0;
for(;;) {
signalHandler->setMsg(R"_(p_earlier(A,C) :- 
   p_earlier(A,B),
   p_earlier(B,C).
in file input.dl [3:1-3:50])_");
if(!(rel_delta_p_earlier_a8001e593b7d88d7->empty()) && !(rel_p_earlier_58b11d5a418636a9->empty())) {
[&](){
CREATE_OP_CONTEXT(rel_delta_p_earlier_a8001e593b7d88d7_op_ctxt,rel_delta_p_earlier_a8001e593b7d88d7->createContext());
CREATE_OP_CONTEXT(rel_new_p_earlier_b29f1557490eb09b_op_ctxt,rel_new_p_earlier_b29f1557490eb09b->createContext());
CREATE_OP_CONTEXT(rel_p_earlier_58b11d5a418636a9_op_ctxt,rel_p_earlier_58b11d5a418636a9->createContext());
for(const auto& env0 : *rel_delta_p_earlier_a8001e593b7d88d7) {
auto range = rel_p_earlier_58b11d5a418636a9->lowerUpperRange_10(Tuple<RamDomain,2>{{ramBitCast(env0[1]), ramBitCast<RamDomain>(MIN_RAM_SIGNED)}},Tuple<RamDomain,2>{{ramBitCast(env0[1]), ramBitCast<RamDomain>(MAX_RAM_SIGNED)}},READ_OP_CONTEXT(rel_p_earlier_58b11d5a418636a9_op_ctxt));
for(const auto& env1 : range) {
if( !(rel_p_earlier_58b11d5a418636a9->contains(Tuple<RamDomain,2>{{ramBitCast(env0[0]),ramBitCast(env1[1])}},READ_OP_CONTEXT(rel_p_earlier_58b11d5a418636a9_op_ctxt))) && !(rel_delta_p_earlier_a8001e593b7d88d7->contains(Tuple<RamDomain,2>{{ramBitCast(env0[1]),ramBitCast(env1[1])}},READ_OP_CONTEXT(rel_delta_p_earlier_a8001e593b7d88d7_op_ctxt)))) {
Tuple<RamDomain,2> tuple{{ramBitCast(env0[0]),ramBitCast(env1[1])}};
rel_new_p_earlier_b29f1557490eb09b->insert(tuple,READ_OP_CONTEXT(rel_new_p_earlier_b29f1557490eb09b_op_ctxt));
}
}
}
}
();}
signalHandler->setMsg(R"_(p_earlier(A,C) :- 
   p_earlier(A,B),
   p_earlier(B,C).
in file input.dl [3:1-3:50])_");
if(!(rel_p_earlier_58b11d5a418636a9->empty()) && !(rel_delta_p_earlier_a8001e593b7d88d7->empty())) {
[&](){
CREATE_OP_CONTEXT(rel_delta_p_earlier_a8001e593b7d88d7_op_ctxt,rel_delta_p_earlier_a8001e593b7d88d7->createContext());
CREATE_OP_CONTEXT(rel_new_p_earlier_b29f1557490eb09b_op_ctxt,rel_new_p_earlier_b29f1557490eb09b->createContext());
CREATE_OP_CONTEXT(rel_p_earlier_58b11d5a418636a9_op_ctxt,rel_p_earlier_58b11d5a418636a9->createContext());
for(const auto& env0 : *rel_p_earlier_58b11d5a418636a9) {
auto range = rel_delta_p_earlier_a8001e593b7d88d7->lowerUpperRange_10(Tuple<RamDomain,2>{{ramBitCast(env0[1]), ramBitCast<RamDomain>(MIN_RAM_SIGNED)}},Tuple<RamDomain,2>{{ramBitCast(env0[1]), ramBitCast<RamDomain>(MAX_RAM_SIGNED)}},READ_OP_CONTEXT(rel_delta_p_earlier_a8001e593b7d88d7_op_ctxt));
for(const auto& env1 : range) {
if( !(rel_p_earlier_58b11d5a418636a9->contains(Tuple<RamDomain,2>{{ramBitCast(env0[0]),ramBitCast(env1[1])}},READ_OP_CONTEXT(rel_p_earlier_58b11d5a418636a9_op_ctxt)))) {
Tuple<RamDomain,2> tuple{{ramBitCast(env0[0]),ramBitCast(env1[1])}};
rel_new_p_earlier_b29f1557490eb09b->insert(tuple,READ_OP_CONTEXT(rel_new_p_earlier_b29f1557490eb09b_op_ctxt));
}
}
}
}
();}
if(rel_new_p_earlier_b29f1557490eb09b->empty()) break;
[&](){
CREATE_OP_CONTEXT(rel_new_p_earlier_b29f1557490eb09b_op_ctxt,rel_new_p_earlier_b29f1557490eb09b->createContext());
CREATE_OP_CONTEXT(rel_p_earlier_58b11d5a418636a9_op_ctxt,rel_p_earlier_58b11d5a418636a9->createContext());
for(const auto& env0 : *rel_new_p_earlier_b29f1557490eb09b) {
Tuple<RamDomain,2> tuple{{ramBitCast(env0[0]),ramBitCast(env0[1])}};
rel_p_earlier_58b11d5a418636a9->insert(tuple,READ_OP_CONTEXT(rel_p_earlier_58b11d5a418636a9_op_ctxt));
}
}
();std::swap(rel_delta_p_earlier_a8001e593b7d88d7, rel_new_p_earlier_b29f1557490eb09b);
rel_new_p_earlier_b29f1557490eb09b->purge();
loop_counter = (ramBitCast<RamUnsigned>(loop_counter) + ramBitCast<RamUnsigned>(RamUnsigned(1)));
iter++;
}
iter = 0;
rel_delta_p_earlier_a8001e593b7d88d7->purge();
rel_new_p_earlier_b29f1557490eb09b->purge();
}

} // namespace  souffle

namespace  souffle {
using namespace souffle;
class Sf_program: public SouffleProgram {
public:
 Sf_program();
 ~Sf_program();
void run();
void runAll(std::string inputDirectoryArg = "",std::string outputDirectoryArg = "",bool performIOArg = true,bool pruneImdtRelsArg = true);
void printAll([[maybe_unused]] std::string outputDirectoryArg = "");
void loadAll([[maybe_unused]] std::string inputDirectoryArg = "");
void dumpInputs();
void dumpOutputs();
SymbolTable& getSymbolTable();
RecordTable& getRecordTable();
void setNumThreads(std::size_t numThreadsValue);
void executeSubroutine(std::string name,const std::vector<RamDomain>& args,std::vector<RamDomain>& ret);
private:
void runFunction(std::string inputDirectoryArg,std::string outputDirectoryArg,bool performIOArg,bool pruneImdtRelsArg);
SymbolTableImpl symTable;
SpecializedRecordTable<0> recordTable;
ConcurrentCache<std::string,std::regex> regexCache;
Own<t_btree_000_ii__0_1__11__10::Type> rel_p_earlier_58b11d5a418636a9;
souffle::RelationWrapper<t_btree_000_ii__0_1__11__10::Type> wrapper_rel_p_earlier_58b11d5a418636a9;
Own<t_btree_000_ii__0_1__11__10::Type> rel_new_p_earlier_b29f1557490eb09b;
Own<t_btree_000_ii__0_1__11__10::Type> rel_delta_p_earlier_a8001e593b7d88d7;
Own<t_btree_000_i__0__1::Type> rel_answer_227ae7ad3b0ead1f;
souffle::RelationWrapper<t_btree_000_i__0__1::Type> wrapper_rel_answer_227ae7ad3b0ead1f;
Stratum_answer_6c655231fec607ba stratum_answer_2f35c27c80acc152;
Stratum_p_earlier_3f10fbf7b3477d6b stratum_p_earlier_3d268a5572d6ce12;
std::string inputDirectory;
std::string outputDirectory;
SignalHandler* signalHandler{SignalHandler::instance()};
std::atomic<RamDomain> ctr{};
std::atomic<std::size_t> iter{};
};
} // namespace  souffle
namespace  souffle {
using namespace souffle;
 Sf_program::Sf_program():
symTable({
  R"_(N12)_",
  R"_(N15)_",
}),
recordTable(),
regexCache(),
rel_p_earlier_58b11d5a418636a9(mk<t_btree_000_ii__0_1__11__10::Type>()),
wrapper_rel_p_earlier_58b11d5a418636a9(0, *rel_p_earlier_58b11d5a418636a9, *this, "p_earlier", std::array<const char *,2>{{"s:symbol","s:symbol"}}, std::array<const char *,2>{{"a0","a1"}}, 0),
rel_new_p_earlier_b29f1557490eb09b(mk<t_btree_000_ii__0_1__11__10::Type>()),
rel_delta_p_earlier_a8001e593b7d88d7(mk<t_btree_000_ii__0_1__11__10::Type>()),
rel_answer_227ae7ad3b0ead1f(mk<t_btree_000_i__0__1::Type>()),
wrapper_rel_answer_227ae7ad3b0ead1f(1, *rel_answer_227ae7ad3b0ead1f, *this, "answer", std::array<const char *,1>{{"i:number"}}, std::array<const char *,1>{{"i"}}, 0),
stratum_answer_2f35c27c80acc152(symTable,recordTable,regexCache,pruneImdtRels,performIO,signalHandler,iter,ctr,inputDirectory,outputDirectory,*rel_answer_227ae7ad3b0ead1f,*rel_p_earlier_58b11d5a418636a9),
stratum_p_earlier_3d268a5572d6ce12(symTable,recordTable,regexCache,pruneImdtRels,performIO,signalHandler,iter,ctr,inputDirectory,outputDirectory,*rel_delta_p_earlier_a8001e593b7d88d7,*rel_new_p_earlier_b29f1557490eb09b,*rel_p_earlier_58b11d5a418636a9){
addRelation("p_earlier", wrapper_rel_p_earlier_58b11d5a418636a9, true, false);
addRelation("answer", wrapper_rel_answer_227ae7ad3b0ead1f, false, true);
}

 Sf_program::~Sf_program(){
}

void Sf_program::runFunction(std::string inputDirectoryArg,std::string outputDirectoryArg,bool performIOArg,bool pruneImdtRelsArg){

    this->inputDirectory  = std::move(inputDirectoryArg);
    this->outputDirectory = std::move(outputDirectoryArg);
    this->performIO       = performIOArg;
    this->pruneImdtRels   = pruneImdtRelsArg;

    // set default threads (in embedded mode)
    // if this is not set, and omp is used, the default omp setting of number of cores is used.
#if defined(_OPENMP)
    if (0 < getNumThreads()) { omp_set_num_threads(static_cast<int>(getNumThreads())); }
#endif

    signalHandler->set();
// -- query evaluation --
{
 std::vector<RamDomain> args, ret;
stratum_p_earlier_3d268a5572d6ce12.run(args, ret);
}
{
 std::vector<RamDomain> args, ret;
stratum_answer_2f35c27c80acc152.run(args, ret);
}

// -- relation hint statistics --
signalHandler->reset();
}

void Sf_program::run(){
runFunction("", "", false, false);
}

void Sf_program::runAll(std::string inputDirectoryArg,std::string outputDirectoryArg,bool performIOArg,bool pruneImdtRelsArg){
runFunction(inputDirectoryArg, outputDirectoryArg, performIOArg, pruneImdtRelsArg);
}

void Sf_program::printAll([[maybe_unused]] std::string outputDirectoryArg){
try {std::map<std::string, std::string> directiveMap({{R"_(IO)_",R"_(file)_"},{R"_(attributeNames)_",R"_(i)_"},{R"_(auxArity)_",R"_(0)_"},{R"_(name)_",R"_(answer)_"},{R"_(operation)_",R"_(output)_"},{R"_(output-dir)_",R"_(.)_"},{R"_(params)_",R"_({"records": {}, "relation": {"arity": 1, "params": ["i"]}})_"},{R"_(types)_",R"_({"ADTs": {}, "records": {}, "relation": {"arity": 1, "types": ["i:number"]}})_"}});
if (!outputDirectoryArg.empty()) {directiveMap["output-dir"] = outputDirectoryArg;}
IOSystem::getInstance().getWriter(directiveMap, symTable, recordTable)->writeAll(*rel_answer_227ae7ad3b0ead1f);
} catch (std::exception& e) {std::cerr << e.what();exit(1);}
}

void Sf_program::loadAll([[maybe_unused]] std::string inputDirectoryArg){
try {std::map<std::string, std::string> directiveMap({{R"_(IO)_",R"_(file)_"},{R"_(attributeNames)_",R"_(a0	a1)_"},{R"_(auxArity)_",R"_(0)_"},{R"_(fact-dir)_",R"_(.)_"},{R"_(name)_",R"_(p_earlier)_"},{R"_(operation)_",R"_(input)_"},{R"_(params)_",R"_({"records": {}, "relation": {"arity": 2, "params": ["a0", "a1"]}})_"},{R"_(types)_",R"_({"ADTs": {}, "records": {}, "relation": {"arity": 2, "types": ["s:symbol", "s:symbol"]}})_"}});
if (!inputDirectoryArg.empty()) {directiveMap["fact-dir"] = inputDirectoryArg;}
IOSystem::getInstance().getReader(directiveMap, symTable, recordTable)->readAll(*rel_p_earlier_58b11d5a418636a9);
} catch (std::exception& e) {std::cerr << "Error loading p_earlier data: " << e.what() << '\n';
exit(1);
}
}

void Sf_program::dumpInputs(){
try {std::map<std::string, std::string> rwOperation;
rwOperation["IO"] = "stdout";
rwOperation["name"] = "p_earlier";
rwOperation["types"] = R"_({"relation": {"arity": 2, "auxArity": 0, "types": ["s:symbol", "s:symbol"]}})_";
IOSystem::getInstance().getWriter(rwOperation, symTable, recordTable)->writeAll(*rel_p_earlier_58b11d5a418636a9);
} catch (std::exception& e) {std::cerr << e.what();exit(1);}
}

void Sf_program::dumpOutputs(){
try {std::map<std::string, std::string> rwOperation;
rwOperation["IO"] = "stdout";
rwOperation["name"] = "answer";
rwOperation["types"] = R"_({"relation": {"arity": 1, "auxArity": 0, "types": ["i:number"]}})_";
IOSystem::getInstance().getWriter(rwOperation, symTable, recordTable)->writeAll(*rel_answer_227ae7ad3b0ead1f);
} catch (std::exception& e) {std::cerr << e.what();exit(1);}
}

SymbolTable& Sf_program::getSymbolTable(){
return symTable;
}

RecordTable& Sf_program::getRecordTable(){
return recordTable;
}

void Sf_program::setNumThreads(std::size_t numThreadsValue){
SouffleProgram::setNumThreads(numThreadsValue);
symTable.setNumLanes(getNumThreads());
recordTable.setNumLanes(getNumThreads());
regexCache.setNumLanes(getNumThreads());
}

void Sf_program::executeSubroutine(std::string name,const std::vector<RamDomain>& args,std::vector<RamDomain>& ret){
if (name == "answer") {
stratum_answer_2f35c27c80acc152.run(args, ret);
return;}
if (name == "p_earlier") {
stratum_p_earlier_3d268a5572d6ce12.run(args, ret);
return;}
fatal(("unknown subroutine " + name).c_str());
}

} // namespace  souffle
namespace souffle {
SouffleProgram *newInstance_program(){return new  souffle::Sf_program;}
SymbolTable *getST_program(SouffleProgram *p){return &reinterpret_cast<souffle::Sf_program*>(p)->getSymbolTable();}
} // namespace souffle

#ifndef __EMBEDDED_SOUFFLE__
#include "souffle/CompiledOptions.h"
int main(int argc, char** argv)
{
try{
souffle::CmdOptions opt(R"_(/home/dhilipsiva/projects/dhilipsiva/nibli/paper/results/evaluation/inputs/comparison-chain-16-forward-s83-d10-m1-verdict/input.dl)_",
R"_()_",
R"_()_",
false,
R"_()_",
1);
if (!opt.parse(argc,argv)) return 1;
souffle::Sf_program obj;
#if defined(_OPENMP) 
obj.setNumThreads(opt.getNumJobs());

#endif
obj.runAll(opt.getInputFileDir(), opt.getOutputFileDir());
return 0;
} catch(std::exception &e) { souffle::SignalHandler::instance()->error(e.what());}
}
#endif

namespace  souffle {
using namespace souffle;
class factory_Sf_program: souffle::ProgramFactory {
public:
souffle::SouffleProgram* newInstance();
 factory_Sf_program();
private:
};
} // namespace  souffle
namespace  souffle {
using namespace souffle;
souffle::SouffleProgram* factory_Sf_program::newInstance(){
return new  souffle::Sf_program();
}

 factory_Sf_program::factory_Sf_program():
souffle::ProgramFactory("program"){
}

} // namespace  souffle
namespace souffle {

#ifdef __EMBEDDED_SOUFFLE__
extern "C" {
souffle::factory_Sf_program __factory_Sf_program_instance;
}
#endif
} // namespace souffle

