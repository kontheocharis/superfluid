const { Buffer } = require("node:buffer");
const prompt = require("prompt-sync")();

const js_null = null;
const js_undefined = undefined;
const js_true = true;
const js_false = false;
const js_zero = 0;
const js_one = 1;

const js_plus = (a, b) => a + b;
const js_minus = (a, b) => a - b;
const js_times = (a, b) => a * b;
const js_div = (a, b) => a / b;
const js_mod = (a, b) => a % b;
const js_pow = (a, b) => a ** b;
const js_neg = (a) => -a;

const js_eq = (a, b) => a == b;
const js_eqq = (a, b) => a === b;
const js_neq = (a, b) => a != b;
const js_neqq = (a, b) => a !== b;
const js_lt = (a, b) => a < b;
const js_lte = (a, b) => a <= b;
const js_gt = (a, b) => a > b;
const js_gte = (a, b) => a >= b;

const js_and = (a, b) => a && b;
const js_or = (a, b) => a || b;
const js_not = (a) => !a;

const js_cond = (c, t, f) => (c ? t : f);
const js_typeof = (e) => typeof e;
const js_lazy = (e) => () => e;

const js_app = (f, as) => f(...as);
const js_multi_app = (f, as) => f(...as);

const js_switch = (e, cs) => {
  for (const [c, s] of cs) {
    if (e === c) return s;
  }
};

const js_obj = (ps) => {
  const obj = {};
  for (const [s, e] of ps) {
    obj[s] = e;
  }
  return obj;
};

const js_invoke = (e) => e();

const js_empty_array = [];

const js_array_extend_l = (a, b) => [a, ...b];
const js_array_extend_r = (a, b) => [...a, b];

const js_length = (a) => a.length;

const js_slice = (a, b, c) => a.slice(b, c);

const js_fold = (f, i, a) => a.reduce(f, i);

const js_map = (f, a) => a.map(f);

var Unit = null;
var tt = [0];
var Sigma = (x17140) => (x17151) => null;
var pair = (x17160) => (x17171) => [0, x1716, x1717];
var dup = (A0) => (a1) => (pair)(a1, a1);
var fst = (A0) => (B1) => (p2) => (() => {
  switch ((p2)[0]) {
    case 0: return ((a3) => (b4) => a3)((p2)[1], (p2)[2]);
  }
})();
var snd = (_0) => (B1) => (p2) => (() => {
  switch ((p2)[0]) {
    case 0: return ((a3) => (b4) => b4)((p2)[1], (p2)[2]);
  }
})();
var id = (A0) => (a1) => a1;
var if_then_else = (A0) => (b1) => (t2) => (f3) => (js_if_dep)((x784) => A0, b1, (_4) => (t2)(tt), (_4) => (f3)(tt));
var debug_print = (A0) => (B1) => (a2) => (b3) => (unsafe_io)(B1, (io_bind)(Unit, B1, (js_console_log)(A0, a2), (_4) => (io_return)(B1, b3)));
var Maybe = (x17180) => null;
var nothing = [0];
var just = (x17190) => [1, x1719];
var Either = (x17200) => (x17211) => null;
var left = (x17220) => [0, x1722];
var right = (x17230) => [1, x1723];
var Empty = null;
var VOID = (A0) => (m1) => (() => {
  switch ((m1)[0]) {
    
  }
})();
var Dec = (x17240) => null;
var yes = (x17250) => [0, x1725];
var no = (x17260) => [1, x1726];
var sub = (m0) => (n1) => (js_zero_or_pos)((x1772) => JsUint, (_2) => m0, (x16862) => (js_zero_or_pos)((x1803) => JsUint, (_3) => js_uint_zero, (x16873) => (sub)(x16873, x16862), m0), n1);
var upgrade = (n0) => (k1) => (js_zero_or_pos)((m2) => null, (_2) => (id)((JsBoundedUint)(n0)), (x16882) => (x3) => (js_bounded_uint_inc)((js_uint_plus)(x16882, n0), (upgrade)(n0, x16882, x3)), k1);
var type = (A0) => (_1) => A0;
var find = (A0) => (p1) => (xs2) => (js_array_switch_l)(A0, (x4093) => (Maybe)(A0), (_3) => nothing, (a3) => (xs4) => (js_if_dep)((x4265) => (Maybe)(A0), (p1)(xs4), (_5) => (just)(xs4), (_5) => (find)(A0, p1, a3)), xs2);
var subst = (A0) => (x1) => (y2) => (P3) => (e4) => (unsafe_cast)(null, null, (id)((P3)((conjure)(A0))));
var subst_type = (A0) => (B1) => (subst)(null, A0, B1, (X2) => X2);
var cong = (A0) => (B1) => (x2) => (y3) => (f4) => (e5) => (unsafe_cast)(JsUndefined, JsUndefined, js_undefined);
var sym = (A0) => (x1) => (y2) => (e3) => (unsafe_cast)(JsUndefined, JsUndefined, js_undefined);
var z_neq_s = (n0) => (p1) => (subst)(JsUint, js_uint_zero, (js_uint_plus)(js_uint_one, n0), (n2) => (js_zero_or_pos)((x6433) => null, (_3) => Unit, (x17003) => Empty, n2), p1, tt);
var co_sym = (A0) => (x1) => (y2) => (m3) => (p4) => (m3)((sym)(A0, y2, x1, p4));
var s_inj = (n0) => (m1) => (e2) => (subst)(JsUint, (js_uint_plus)(js_uint_one, n0), (js_uint_plus)(js_uint_one, m1), (x3) => JsUndefined, e2, js_undefined);
var s_co_cong = (x0) => (y1) => (m2) => (p3) => (m2)((s_inj)(x0, y1, p3));
var nat_eq_dep = (n0) => (m1) => (js_zero_or_pos)((n2) => (Dec)(JsUndefined), (_2) => (js_zero_or_pos)((m3) => (Dec)(JsUndefined), (_3) => (yes)(js_undefined), (x17043) => (no)((z_neq_s)(x17043)), m1), (x17032) => (js_zero_or_pos)((m3) => (Dec)(JsUndefined), (_3) => (no)((co_sym)(JsUint, js_uint_zero, (js_uint_plus)(js_uint_one, x17032), (z_neq_s)(x17032))), (x17063) => (() => {
  switch (((nat_eq_dep)(x17032, x17063))[0]) {
    case 0: return ((e4) => (yes)((cong)(JsUint, JsUint, x17032, x17063, (n5) => (js_uint_plus)(js_uint_one, n5), e4)))(((nat_eq_dep)(x17032, x17063))[1]);
    case 1: return ((f4) => (no)((s_co_cong)(x17032, x17063, f4)))(((nat_eq_dep)(x17032, x17063))[1]);
  }
})(), m1), n0);
var dec_to_bool = (A0) => (x8231) => (() => {
  switch ((x8231)[0]) {
    case 0: return ((x8252) => js_true)((x8231)[1]);
    case 1: return ((x8282) => js_false)((x8231)[1]);
  }
})();
var lte = (m0) => (n1) => (js_zero_or_pos)((x8332) => JsBool, (_2) => js_true, (x17072) => (js_zero_or_pos)((x8363) => JsBool, (_3) => js_false, (x17083) => (lte)(x17072, x17083), n1), m0);
var lt = (m0) => (n1) => (js_and)((js_not)((js_eqq)(JsUint, JsUint, m0, n1)), (lte)(m0, n1));
var bool_eq = (a0) => (b1) => (js_if_dep)((x8402) => JsBool, a0, (_2) => (js_if_dep)((x8413) => JsBool, b1, (_3) => js_true, (_3) => js_false), (_2) => (js_if_dep)((x8423) => JsBool, b1, (_3) => js_false, (_3) => js_true));
var Char = null;
var char_from_num = (x17270) => [0, x1727];
var STRING = null;
var snil = [0];
var scons = (x17280) => (x17291) => [1, x1728, x1729];
var Word = (JsBoundedUint)(65536);
var Byte = (JsBoundedUint)(256);
var word_to_nat = (n0) => (js_forget_bound)(65536, n0);
var Holds = (b0) => JsUndefined;
var byte_list_length = (l0) => (js_if)(JsUint, (js_eqq)(JsUint, JsUint, (js_buffer_byte_length)(l0), 0), (_1) => (unsafe_complete)(JsBuffer, (x10032) => JsUint, l0, js_buffer_empty, js_uint_zero), (_1) => (unsafe_complete)(JsBuffer, (x10032) => JsUint, l0, (fst)(JsBuffer, (x10382) => Unit, (js_buffer_run)(Unit, (js_buffer_alloc)((js_uint_plus)((js_buffer_byte_length)((js_buffer_subarray)(l0, 1, (js_buffer_byte_length)(l0))), 1)), (js_buffer_bind)(Unit, Unit, (js_buffer_copy)((js_buffer_subarray)(l0, 1, (js_buffer_byte_length)(l0)), 0, (js_buffer_byte_length)((js_buffer_subarray)(l0, 1, (js_buffer_byte_length)(l0))), 1), (_2) => (js_buffer_write_uint8)((js_forget_bound)(256, (js_bound_trust_me)(256, (js_buffer_read_uint8)(l0, 0))), 0)))), (js_uint_plus)(js_uint_one, (byte_list_length)((js_bound_trust_me)(256, (js_buffer_read_uint8)(l0, 0))))));
var byte_vec_length = (n0) => (b1) => n0;
var Reprs = (l0) => (T1) => (js_zero_or_pos)((x13482) => null, (_2) => T1, (x17112) => (Reprs)(x17112, T1), l0);
var reprs = (T0) => (l1) => (t2) => (js_zero_or_pos)((l3) => (Reprs)(l3, T0), (_3) => t2, (x17123) => (reprs)(T0, x17123, t2), l1);
var unreprs = (T0) => (l1) => (js_zero_or_pos)((l2) => null, (_2) => (id)((Reprs)(js_uint_zero, T0)), (x17132) => (r3) => (unreprs)(T0, x17132, r3), l1);
var repr_subst = (A0) => (B1) => (subst_type)(A0, B1);
var repr_subst_p_ = (A0) => (B1) => (p2) => (subst_type)(B1, A0, (sym)(null, A0, B1, p2));
var ReprBy = (T0) => (U1) => (Sigma)(JsUint, (l2) => JsUndefined);
var reprs_subst = (A0) => (B1) => (r2) => (a3) => (() => {
  switch ((r2)[0]) {
    case 0: return ((l4) => (p5) => (subst_type)((Reprs)(l4, A0), B1, p5, (reprs)(A0, l4, a3)))((r2)[1], (r2)[2]);
  }
})();
var reprs_subst_p_ = (A0) => (B1) => (r2) => (b3) => (() => {
  switch ((r2)[0]) {
    case 0: return ((l4) => (p5) => (unreprs)(A0, l4, (subst_type)(B1, (Reprs)(l4, A0), (sym)(null, (Reprs)(l4, A0), B1, p5), b3)))((r2)[1], (r2)[2]);
  }
})();
var Time = null;
var millis = (x17300) => [0, x1730];
var current_time = null;
var nat_from_digits = (n0) => (null)(n0);
var nat_to_fin_trunc = (n0) => (null)(n0);
var trunc_buffer = (n0) => (m1) => (null)(m1, n0);
var string_bytes = null;
var Response = (x17310) => null;
var ok = (x17320) => [0, x1732];
var drop = [1];
var error = (x17330) => [2, x1733];
var UdpHeader = null;
var udp_header = (x17340) => (x17351) => (x17362) => (x17373) => [0, x1734, x1735, x1736, x1737];
var udp_len = (x15110) => (() => {
  switch ((x15110)[0]) {
    case 0: return ((src_port1) => (dst_port2) => (len3) => (checksum4) => (js_forget_bound)(65536, len3))((x15110)[1], (x15110)[2], (x15110)[3], (x15110)[4]);
  }
})();
var UdpPacket = null;
var udp_packet = (x17380) => (x17391) => [0, x1738, x1739];
var udp_server = null;
var FizzBuzz = null;
var fizz = [0];
var buzz = [1];
var fizzbuzz = [2];
var get_fizzbuzz = (n0) => (js_if_dep)((x15381) => (Maybe)(FizzBuzz), (js_eqq)(JsUint, JsUint, (js_uint_mod)(n0, 15), 0), (_1) => (just)(fizzbuzz), (_1) => (js_if_dep)((x15402) => (Maybe)(FizzBuzz), (js_eqq)(JsUint, JsUint, (js_uint_mod)(n0, 3), 0), (_2) => (just)(fizz), (_2) => (js_if_dep)((x15423) => (Maybe)(FizzBuzz), (js_eqq)(JsUint, JsUint, (js_uint_mod)(n0, 5), 0), (_3) => (just)(buzz), (_3) => nothing)));
var MY_PORT = 1234;
var reply_to = (h0) => (l1) => (b2) => (() => {
  switch ((h0)[0]) {
    case 0: return ((src_port3) => (dst_port4) => (len5) => (checksum6) => (udp_packet)((udp_header)(MY_PORT, src_port3, (nat_to_fin_trunc)(65536, l1), checksum6), (trunc_buffer)(l1, 65536, b2)))((h0)[1], (h0)[2], (h0)[3], (h0)[4]);
  }
})();
var handle_packet = (x15920) => (() => {
  switch ((x15920)[0]) {
    case 0: return ((h1) => (contents2) => (() => {
      switch (((nat_from_digits)((udp_len)(h1), contents2))[0]) {
        case 0: return ((io_return)((Response)(UdpPacket), (error)("Invalid number in packet")))();
        case 1: return ((n3) => (() => {
          switch (((get_fizzbuzz)(n3))[0]) {
            case 0: return ((() => {
              switch (((string_bytes)("I got nothing"))[0]) {
                case 0: return ((l4) => (b5) => (io_return)((Response)(UdpPacket), (ok)((reply_to)(h1, l4, b5))))(((string_bytes)("I got nothing"))[1], ((string_bytes)("I got nothing"))[2]);
              }
            })())();
            case 1: return ((fb4) => (() => {
              switch ((fb4)[0]) {
                case 0: return ((() => {
                  switch (((string_bytes)("Fizz"))[0]) {
                    case 0: return ((l5) => (b6) => (io_return)((Response)(UdpPacket), (ok)((reply_to)(h1, l5, b6))))(((string_bytes)("Fizz"))[1], ((string_bytes)("Fizz"))[2]);
                  }
                })())();
                case 1: return ((() => {
                  switch (((string_bytes)("Buzz"))[0]) {
                    case 0: return ((l5) => (b6) => (io_return)((Response)(UdpPacket), (ok)((reply_to)(h1, l5, b6))))(((string_bytes)("Buzz"))[1], ((string_bytes)("Buzz"))[2]);
                  }
                })())();
                case 2: return ((() => {
                  switch (((string_bytes)("FizzBuzz"))[0]) {
                    case 0: return ((l5) => (b6) => (io_return)((Response)(UdpPacket), (ok)((reply_to)(h1, l5, b6))))(((string_bytes)("FizzBuzz"))[1], ((string_bytes)("FizzBuzz"))[2]);
                  }
                })())();
              }
            })())(((get_fizzbuzz)(n3))[1]);
          }
        })())(((nat_from_digits)((udp_len)(h1), contents2))[1]);
      }
    })())((x15920)[1], (x15920)[2]);
  }
})();
var main = (udp_server)(handle_packet);
(main)()