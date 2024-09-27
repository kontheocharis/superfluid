// boot.js
const { Buffer } = require("buffer");

// Type system
const Type = null;

// Equality
const Equal = (A) => (x) => (y) => null;

// Primitive types
const JsUnion = (A) => (B) => null;
const JsNull = null;
const JsUndefined = null;
const JsBool = null;
const JsArray = (T) => null;
const JsBigInt = null;
const JsUint = null;
const JsBoundedUint = (n) => null;
const JsNumber = null;
const JsString = null;

// Primitive values
const js_null = null;
const js_undefined = undefined;
const js_true = true;
const js_false = false;

// Conditional
const js_if = (A) => (cond) => (thenBranch) => (elseBranch) =>
  cond ? thenBranch() : elseBranch();
const js_if_dep = (A) => (b) => (thenBranch) => (elseBranch) =>
  b ? thenBranch() : elseBranch();

// Array operations
const js_empty_array = (T) => () => [];
const js_array_extend_l = (T) => (x) => (arr) => [x, ...arr];
const js_array_extend_r = (T) => (arr) => (x) => [...arr, x];
const js_array_switch_l =
  (T) => (E) => (emptyCase) => (nonEmptyCase) => (arr) =>
    arr.length === 0 ? emptyCase() : nonEmptyCase(arr[0])(arr.slice(1));
const js_array_switch_r =
  (T) => (E) => (emptyCase) => (nonEmptyCase) => (arr) =>
    arr.length === 0
      ? emptyCase()
      : nonEmptyCase(arr.slice(0, -1))(arr[arr.length - 1]);
const js_slice = (T) => (arr) => (start) => (end) => arr.slice(start, end);
const js_length = (T) => (arr) => arr.length;
const js_map = (A) => (B) => (a) => (fn) => a.map((x, i) => fn([x, i]));
const js_reduce = (T) => (C) => (fn) => (initial) => (arr) =>
  arr.reduce((acc, val) => fn(acc)(val), initial);
const js_index = (T) => (a) => (n) => a[n];

// Number operations
const js_zero = 0;
const js_one = 1;
const js_uint_zero = 0;
const js_uint_one = 1;
const js_plus = (a) => (b) => a + b;
const js_uint_plus = (a) => (b) => a + b;
const js_forget_bound = (n) => (x) => x;
const js_zero_or_pos = (A) => (zeroCase) => (posCase) => (i) =>
  i === 0 ? zeroCase() : posCase(i - 1);
const js_bounded_uint_zero = (n) => 0;
const js_bounded_uint_inc = (n) => (x) => x + 1;
const js_bounded_zero_or_pos = (A) => (zeroCase) => (posCase) => (n) => (i) =>
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
const js_eq = (A) => (B) => (a) => (b) => a == b;
const js_eqq = (A) => (B) => (a) => (b) => a === b;
const js_neq = (A) => (B) => (a) => (b) => a != b;
const js_neqq = (A) => (B) => (a) => (b) => a !== b;
const js_lt = (a) => (b) => a < b;
const js_lte = (a) => (b) => a <= b;
const js_gt = (a) => (b) => a > b;
const js_gte = (a) => (b) => a >= b;

// Boolean operations
const js_and = (a) => (b) => a && b;
const js_or = (a) => (b) => a || b;
const js_not = (a) => !a;

// Error handling
const js_panic = (T) => (msg) => {
  throw new Error(msg);
};

// IO Monad (CPS style)
const IO = (A) => (f) => f;
const io_return = (A) => (x) => (k) => x;
const io_bind = (A) => (B) => (ma) => (f) => (k) => ma((a) => f(a)(k));

// Unsafe IO execution
const unsafe_io = (A) => (io) => {
  let result;
  io((x) => {
    result = x;
  });
  return result;
};

// JS IO operations
const js_console_log = (T) => (x) => (k) => {
  console.log(x);
  k();
};

// JS Buffer operations
const JsBuffer = null;
const JsBufferMod = (A) => (f) => f;

const js_buffer_bind = (A) => (B) => (ma) => (f) => (buf) => {
  const [newBuf, a] = ma(buf);
  return f(a)(newBuf);
};

const js_buffer_return = (A) => (x) => (buf) => [buf, x];

const js_buffer_get = (buf) => [buf, buf];

const js_buffer_set = (newBuf) => () => [newBuf, undefined];

const js_buffer_empty = Buffer.alloc(0);

const js_buffer_run = (A) => (buf) => (mod) => mod(buf);

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
const unsafe_cast = (A) => (B) => (x) => x;
const unsafe_complete = (T) => (E) => (t) => (u) => (h) => h;

const js_bound_trust_me = (n) => (x) => x;

const js_assert_defined = (T) => (x) => x;

const prim = (x) => x;

const conjure = (A) => () => null;

const trust_me = (A) => (x) => (y) => null;
