const { Buffer } = require("node:buffer");
const prompt = require("prompt-sync")();

const jsNull = null;
const jsUndefined = undefined;
const jsTrue = true;
const jsFalse = false;
const jsZero = 0;
const jsOne = 1;

const jsPlus = (a, b) => a + b;
const jsMinus = (a, b) => a - b;
const jsTimes = (a, b) => a * b;
const jsDiv = (a, b) => a / b;
const jsMod = (a, b) => a % b;
const jsPow = (a, b) => a ** b;
const jsNeg = (a) => -a;

const jsEq = (a, b) => a == b;
const jsEqq = (a, b) => a === b;
const jsNeq = (a, b) => a != b;
const jsNeqq = (a, b) => a !== b;
const jsLt = (a, b) => a < b;
const jsLte = (a, b) => a <= b;
const jsGt = (a, b) => a > b;
const jsGte = (a, b) => a >= b;

const jsAnd = (a, b) => a && b;
const jsOr = (a, b) => a || b;
const jsNot = (a) => !a;

const jsCond = (c, t, f) => (c ? t : f);
const jsTypeof = (e) => typeof e;
const jsLazy = (e) => () => e;

const jsApp = (f, as) => f(...as);
const jsMultiApp = (f, as) => f(...as);

const jsSwitch = (e, cs) => {
  for (const [c, s] of cs) {
    if (e === c) return s;
  }
};

const jsObj = (ps) => {
  const obj = {};
  for (const [s, e] of ps) {
    obj[s] = e;
  }
  return obj;
};

const jsInvoke = (e) => e();

const jsEmptyArray = [];

const jsArrayExtendL = (a, b) => [a, ...b];
const jsArrayExtendR = (a, b) => [...a, b];

const jsLength = (a) => a.length;

const jsSlice = (a, b, c) => a.slice(b, c);

const jsFold = (f, i, a) => a.reduce(f, i);

const jsMap = (f, a) => a.map(f);
