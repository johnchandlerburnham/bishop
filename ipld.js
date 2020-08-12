const dagCBOR = require('ipld-dag-cbor')

const Var = (indx)           => ({ctor:"Var",fld1: indx});
const Ref = (cid)            => ({ctor:"Ref",fld1: cid});
const Lam = (body)           => ({ctor:"Lam",fld1: body});
const App = (func,argm)      => ({ctor:"App",fld1: func,fld2: argm});

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
