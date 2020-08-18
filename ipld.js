const dagCBOR = require('ipld-dag-cbor')

const Anon = (term)       => ({$0:"Anon", $1:term})
const Meta = (nams, locs) => ({$0:"Meta", $1:nams, $2:locs})
const Comm = (term)       => ({$0:"Comm", $1:term})

const Def = (comm, anon, meta,ty_anon, ty_meta) =>
             ({ $0:"Def"
              , $1:docs_comm
              , $2:term_anon
              , $3:term_meta
              , $4:type_anon
              , $5:type_meta
              })

const Var = (indx)                => ({$0:"Var",$1:indx});
const Ref = (cid)                 => ({$0:"Ref",$1:cid});
const Lam = (uses,type, body)     => ({$0:"Lam",$1:uses,$2:type,$3:body});
const Let = (uses,type,expr,body) => ({$0:"Let",$1:uses,$2:type,$3:expr,$4:body});
const App = (func,argm)           => ({$0:"App",$1:func,$2:argm});
const Typ = ()                    => ({$0:"Typ"})
const I64 = ()                    => ({$0:"I64"})
const F64 = ()                    => ({$0:"F64"})
const Wrd = (word)                => ({$0:"Wrd",$1:word})
const Dbl = (word)                => ({$0:"Dbl",$1:word})
const Opr = (prim, argx, argy)    => ({$0:"Opr",$1:prim,$2:argx,$3:argy});
const Ite = (cond, btru, bfls)    => ({$0:"Ite",$1:cond,$2:btru,$3:bfls});
const All = ()                    => ({$0:"All",$1:uses,$2:type,$3:body});
const Slf = (body)                => ({$0:"Slf",$1:body})
const Eli = (body)                => ({$0:"Eli",$1:body})
const New = (type, body)          => ({$0:"New",$1:type,$2:body})

async function test() {
  var id = Lam(Var(0));
  var cbor = await dagCBOR.util.serialize(id);
  console.log(cbor);
  var cid  = await dagCBOR.util.cid(cbor, {hashAlg: 'blake2b-256', version: 1});
  console.log(cid);

  var app_id = App(id,Ref(cid))
  var cbor = await dagCBOR.util.serialize(app_id);
  console.log(cbor);
  var cid  = await dagCBOR.util.cid(cbor, {hashAlg: 'blake2b-256', version: 1});
  console.log(cid);
};
test();
//console.log(id_cid)
