// boot.js
const { Buffer } = require("buffer");

// Type system
const Type = null;

// Equality
const Equal = (x) => (y) => null;

// Primitive types
const JsUnion = null;
const JsNull = null;
const JsUndefined = null;
const JsBool = null;
const JsArray = null;
const JsBigInt = null;
const JsUint = null;
const JsBoundedUint = null;
const JsNumber = null;
const JsString = null;

// Primitive values
const js_null = null;
const js_undefined = undefined;
const js_true = true;
const js_false = false;

// Conditional
const js_if = (cond) => (thenBranch) => (elseBranch) =>
  cond ? thenBranch() : elseBranch();
const js_if_dep = (b) => (thenBranch) => (elseBranch) =>
  b ? thenBranch() : elseBranch();

// Array operations
const js_empty_array = [];
const js_array_extend_l = (x) => (arr) => [x, ...arr];
const js_array_extend_r = (arr) => (x) => [...arr, x];
const js_array_switch_l = (emptyCase) => (nonEmptyCase) => (arr) =>
  arr.length === 0 ? emptyCase() : nonEmptyCase(arr[0])(arr.slice(1));
const js_array_switch_r = (emptyCase) => (nonEmptyCase) => (arr) =>
  arr.length === 0
    ? emptyCase()
    : nonEmptyCase(arr.slice(0, -1))(arr[arr.length - 1]);
const js_slice = (arr) => (start) => (end) => arr.slice(start, end);
const js_length = (arr) => arr.length;
const js_map = (a) => (fn) => a.map((x, i) => fn([x, i]));
const js_reduce = (fn) => (initial) => (arr) =>
  arr.reduce((acc, val) => fn(acc)(val), initial);
const js_index = (a) => (n) => a[n];

// Number operations
const js_zero = 0;
const js_one = 1;
const js_uint_zero = 0;
const js_uint_one = 1;
const js_plus = (a) => (b) => a + b;
const js_uint_plus = (a) => (b) => a + b;
const js_forget_bound = (x) => x;
const js_zero_or_pos = (zeroCase) => (posCase) => (i) =>
  i === 0 ? zeroCase() : posCase(i - 1);
const js_bounded_uint_zero = 0;
const js_bounded_uint_inc = (x) => x + 1;
const js_bounded_zero_or_pos = (zeroCase) => (posCase) => (n) => (i) =>
  i === 0 ? zeroCase(n) : posCase(n)(i - 1);
const js_minus = (a) => (b) => a - b;
const js_times = (a) => (b) => a * b;
const js_uint_times = (a) => (b) => a * b;
const js_div = (a) => (b) => a / b;
const js_mod = (a) => (b) => a % b;
const js_uint_mod = (a) => (b) => a % b;
const js_uint_div = (a) => (b) => Math.floor(a / b);
const js_pow = (a) => (b) => Math.pow(a, b);
const js_uint_pow = (a) => (b) => Math.pow(a, b);
const js_neg = (a) => -a;

// Comparison operations
const js_eq = (a) => (b) => a == b;
const js_eqq = (a) => (b) => a === b;
const js_neq = (a) => (b) => a != b;
const js_neqq = (a) => (b) => a !== b;
const js_lt = (a) => (b) => a < b;
const js_lte = (a) => (b) => a <= b;
const js_gt = (a) => (b) => a > b;
const js_gte = (a) => (b) => a >= b;

// Boolean operations
const js_and = (a) => (b) => a && b;
const js_or = (a) => (b) => a || b;
const js_not = (a) => !a;

// Error handling
const js_panic = (msg) => {
  throw new Error(msg);
};

// IO Monad (CPS style)
const IO = (f) => f;
const io_return = (x) => (k) => x;
const io_bind = (ma) => (f) => (k) => ma((a) => f(a)(k));

// Unsafe IO execution
const unsafe_io = (io) => {
  let result;
  io((x) => {
    result = x;
  });
  return result;
};

// JS IO operations
const js_console_log = (x) => (k) => {
  console.log(x);
  k();
};

// JS Buffer operations
const JsBuffer = null;
const JsBufferMod = (f) => f;

const js_buffer_bind = (ma) => (f) => (buf) => {
  const [newBuf, a] = ma(buf);
  return f(a)(newBuf);
};

const js_buffer_return = (x) => (buf) => [buf, x];

const js_buffer_get = (buf) => [buf, buf];

const js_buffer_set = (newBuf) => () => [newBuf, undefined];

const js_buffer_empty = Buffer.alloc(0);

const js_buffer_run = (buf) => (mod) => mod(buf);

const js_buffer_alloc = (byteLength) => Buffer.alloc(byteLength);

const js_buffer_byte_length = (buf) => buf.byteLength;

const js_buffer_copy =
  (source) => (sourceStart) => (sourceEnd) => (start) => (buf) => {
    source.copy(buf, start, sourceStart, sourceEnd);
    return [buf, undefined];
  };

const js_buffer_write_uint16_be = (value) => (offset) => (buf) => {
  buf.writeUInt16BE(value, offset);
  return [buf, undefined];
};

const js_buffer_write_uint8 = (value) => (offset) => (buf) => {
  buf.writeUInt8(value, offset);
  return [buf, undefined];
};

const js_buffer_read_uint16_be = (buffer) => (offset) =>
  buffer.readUInt16BE(offset);

const js_buffer_read_uint8 = (buffer) => (offset) => buffer.readUInt8(offset);

const js_buffer_subarray = (buffer) => (start) => (end) =>
  buffer.subarray(start, end);

// Unsafe operations
const unsafe_cast = (x) => x;
const unsafe_complete = (h) => h;

const js_bound_trust_me = (x) => x;

const js_assert_defined = (x) => x;

const prim = (x) => x;

const conjure = null;

const trust_me = null;
