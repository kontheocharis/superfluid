var { Buffer } = require('node:buffer');
var prompt = require('prompt-sync')();
var id = (v00) => (a5) => a5;
var if_then_else = (A12) => (b13) => (t14) => (f15) => (b13) ? ((t14)(["tt"])) : ((f15)(["tt"]));
var js_two = (1) + (1);
var js_four = ((1) + (1)) * ((1) + (1));
var js_six = (((1) + (1)) * ((1) + (1))) + ((1) + (1));
var js_eight = (((1) + (1)) * ((1) + (1))) * (((1) + (1)) * ((1) + (1)));
var debug_print = (v11) => (a120) => (() => ((console).log)(a120));
var void = (v2121) => (m169) => (() => {
  switch ((m169)[0]) {
    
  }
})();
var sub = (m187) => (n188) => ((n188) === (0)) ? (m187) : (((m187) === (0)) ? (0) : (((sub)((m187) - (1)))((n188) - (1))));
var find = (v5454) => (p286) => (xs287) => (() => {
  var l_p_480 = xs287;
  return (((l_p_480).length) === (0)) ? (null) : (((p286)((l_p_480)[0])) ? ((l_p_480)[0]) : ((((find)(null))(p286))((l_p_480).slice(1, (l_p_480).length))));
})();
var subst = (v7575) => (v7676) => (v7777) => (P332) => (e333) => (p334) => (() => {
  switch ((e333)[0]) {
    case "refl": return p334;
  }
})();
var cong = (v8282) => (v8383) => (v8484) => (v8585) => (f343) => (e344) => (() => {
  switch ((e344)[0]) {
    case "refl": return ["refl", v8383, (f343)((e344)[(1) + ((1) + (0))])];
  }
})();
var sym = (v9292) => (v9393) => (v9494) => (e350) => (() => {
  switch ((e350)[0]) {
    case "refl": return ["refl", (e350)[(1) + (0)], (e350)[(1) + ((1) + (0))]];
  }
})();
var z_neq_s = (v100100) => (p354) => ((((((subst)(null))(0))((1) + (v100100)))((n356) => ((n356) === (0)) ? (null) : (null)))(p354))(["tt"]);
var co_sym = (v110110) => (v111111) => (v112112) => (m366) => (p367) => (m366)(((((sym)(v110110))(v112112))(v111111))(p367));
var s_inj = (v121121) => (v122122) => (e372) => (() => {
  switch ((e372)[0]) {
    case "refl": return ["refl", null, v121121];
  }
})();
var s_co_cong = (v129129) => (v130130) => (m379) => (p380) => (m379)((((s_inj)(v129129))(v130130))(p380));
var nat_eq = (n384) => (m385) => ((n384) === (0)) ? (((m385) === (0)) ? (["yes", null, ["refl", null, 0]]) : (((m385) === (0)) ? (["yes", null, ["refl", null, 0]]) : (["no", null, (z_neq_s)((m385) - (1))]))) : (((m385) === (0)) ? (["no", null, ((((co_sym)(null))(0))((1) + ((n384) - (1))))((z_neq_s)((n384) - (1)))]) : ((() => {
  switch ((((nat_eq)((n384) - (1)))((m385) - (1)))[0]) {
    case "yes": return ["yes", null, ((((((cong)(null))(null))((n384) - (1)))((m385) - (1)))((n429) => (1) + (n429)))((((nat_eq)((n384) - (1)))((m385) - (1)))[(1) + ((1) + (0))])];
    case "no": return ["no", null, (((s_co_cong)((n384) - (1)))((m385) - (1)))((((nat_eq)((n384) - (1)))((m385) - (1)))[(1) + ((1) + (0))])];
  }
})()));
var minus_one = (n4) => (f5) => ((f5) === (0)) ? (((n4) === (0)) ? (({ throw new Error('impossible'); })()) : ((n4) - (1))) : (((n4) === (0)) ? (({ throw new Error('impossible'); })()) : ((n4) - (1)));
(main)()