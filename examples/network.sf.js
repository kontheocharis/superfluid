const { Buffer } = require('node:buffer');
const prompt = require('prompt-sync')();
const id = (A) => (a) => a;
const if_then_else = (A) => (b) => (t) => (f) => (b) ? ((t)(["tt"])) : ((f)(["tt"]));
const js_two = (1) + (1);
const js_four = ((1) + (1)) * ((1) + (1));
const js_six = (((1) + (1)) * ((1) + (1))) + ((1) + (1));
const js_eight = (((1) + (1)) * ((1) + (1))) * (((1) + (1)) * ((1) + (1)));
const debug_print = (A) => (a) => (() => ((console).log)(a));
const sub = (m) => (n) => ((n) === (0)) ? (m) : (((m) === (0)) ? (0) : (((sub)((m) - (1)))((n) - (1))));
const find = (A) => (p) => (xs) => (((xs).length) === (0)) ? (null) : (((p)((xs)[0])) ? ((xs)[0]) : ((((find)(A))(p))((xs).slice(1, (xs).length))));
const Char = null;
const STRING = null;
const two = (1) + ((1) + (0));
const two_to_the_sixteen = (two) ** ((two) ** ((two) ** (two)));
const field_len = two_to_the_sixteen;
const byte_len = two_to_the_sixteen;
const Word = null;
const OWN_PORT = (1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + ((1) + (0))))))))));
const handle_packet = (p) => (() => {
  const len = ((p).readUInt16BE)(((1) + (1)) * ((1) + (1)));
  return (((((p).readUInt16BE)(0)) % ((1) + (1))) === (0)) ? ((() => {
    const new_p = (() => {
      const total_len = (len) + ((((1) + (1)) * ((1) + (1))) * (((1) + (1)) * ((1) + (1))));
      const b = (Buffer.allocUnsafe)(total_len);
      const b_p_ = (((b).writeUInt16BE)(((p).readUInt16BE)(0), 0), b);
      const b_p__p_ = (((b_p_).writeUInt16BE)(((p).readUInt16BE)((1) + (1)), (1) + (1)), b_p_);
      const b_p__p__p_ = (((b_p__p_).writeUInt16BE)(len, ((1) + (1)) * ((1) + (1))), b_p__p_);
      const b_p__p__p__p_ = (((b_p__p__p_).writeUInt16BE)(((p).readUInt16BE)((((1) + (1)) * ((1) + (1))) + ((1) + (1))), (((1) + (1)) * ((1) + (1))) + ((1) + (1))), b_p__p__p_);
      const b_p__p__p__p__p_ = (((((p).subarray)((((1) + (1)) * ((1) + (1))) * (((1) + (1)) * ((1) + (1))), ((((1) + (1)) * ((1) + (1))) * (((1) + (1)) * ((1) + (1)))) + (len))).copy)(b_p__p__p__p_, (((1) + (1)) * ((1) + (1))) * (((1) + (1)) * ((1) + (1))), 0, len), ((p).subarray)((((1) + (1)) * ((1) + (1))) * (((1) + (1)) * ((1) + (1))), ((((1) + (1)) * ((1) + (1))) * (((1) + (1)) * ((1) + (1)))) + (len)));
      return b_p__p__p__p_;
    })();
    return new_p;
  })()) : (null);
})();
const main = (() => {
  const test_packet = (() => {
    const total_len = (0) + ((((1) + (1)) * ((1) + (1))) * (((1) + (1)) * ((1) + (1))));
    const b = (Buffer.allocUnsafe)(total_len);
    const b_p_ = (((b).writeUInt16BE)((1) + ((1) + (0)), 0), b);
    const b_p__p_ = (((b_p_).writeUInt16BE)((1) + ((1) + ((1) + (0))), (1) + (1)), b_p_);
    const b_p__p__p_ = (((b_p__p_).writeUInt16BE)(0, ((1) + (1)) * ((1) + (1))), b_p__p_);
    const b_p__p__p__p_ = (((b_p__p__p_).writeUInt16BE)((1) + ((1) + ((1) + ((1) + ((1) + (0))))), (((1) + (1)) * ((1) + (1))) + ((1) + (1))), b_p__p__p_);
    const b_p__p__p__p__p_ = ((((Buffer.allocUnsafe)(0)).copy)(b_p__p__p__p_, (((1) + (1)) * ((1) + (1))) * (((1) + (1)) * ((1) + (1))), 0, 0), (Buffer.allocUnsafe)(0));
    return b_p__p__p__p_;
  })();
  const result = (handle_packet)(test_packet);
  return (() => (((_) => ((debug_print)(null))(result))((((debug_print)(null))(test_packet))()))());
})();
(main)()