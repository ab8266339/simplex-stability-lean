import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace SimplexFull

def millsPoly4 (u : ℝ) : ℝ := 1-u+3*u^2-15*u^3+105*u^4
def millsPoly5 (u : ℝ) : ℝ := millsPoly4 u-945*u^5

private theorem pow_small {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (n : ℕ) :
    u^(n+1) ≤ u := by
  calc
    u^(n+1) = u^n*u := pow_succ u n
    _ ≤ 1*u := mul_le_mul_of_nonneg_right (pow_le_one₀ hu hu1) hu
    _ = u := one_mul u

theorem millsPoly_bounds {u : ℝ} (hu : 0 < u) (hsmall : u ≤ 1/10000000000) :
    1-u ≤ millsPoly5 u ∧ millsPoly5 u ≤ millsPoly4 u ∧ millsPoly4 u ≤ 1 := by
  have hu1 : u ≤ 1 := by linarith
  have hp3 := pow_small hu.le hu1 2
  have hb5 : 0 ≤ 3-15*u+105*u^2-945*u^3 := by
    nlinarith [sq_nonneg u]
  have hb4 : 0 ≤ 1-3*u+15*u^2-105*u^3 := by
    nlinarith [sq_nonneg u]
  have he5 : millsPoly5 u-(1-u) = u^2*(3-15*u+105*u^2-945*u^3) := by
    unfold millsPoly5 millsPoly4
    ring
  have he4 : 1-millsPoly4 u = u*(1-3*u+15*u^2-105*u^3) := by
    unfold millsPoly4
    ring
  have hn5 := mul_nonneg (sq_nonneg u) hb5
  have hn4 := mul_nonneg hu.le hb4
  have hnm := mul_nonneg (by norm_num : (0:ℝ) ≤ 945) (pow_nonneg hu.le 5)
  rw [← he5] at hn5
  rw [← he4] at hn4
  unfold millsPoly5 at *
  constructor
  · linarith
  constructor <;> linarith

theorem mills_F_poly_pos {u : ℝ} (hu : 0 < u) (hsmall : u ≤ 1/10000000000) :
    0 < (1-u)*(millsPoly4 u)^2-3*millsPoly4 u+2 := by
  have hu1 : u ≤ 1 := by linarith
  have hcoef : 0 < 2-30*u-549*u^2+1155*u^3-4005*u^4+14175*u^5-11025*u^6 := by
    nlinarith [pow_small hu.le hu1 1, pow_small hu.le hu1 3,
      pow_small hu.le hu1 5, pow_nonneg hu.le 3, pow_nonneg hu.le 5]
  calc
    0 < u^3*(2-30*u-549*u^2+1155*u^3-4005*u^4+14175*u^5-11025*u^6) :=
      mul_pos (pow_pos hu 3) hcoef
    _ = (1-u)*(millsPoly4 u)^2-3*millsPoly4 u+2 := by
      unfold millsPoly4
      ring

theorem mills_D_poly_pos {u : ℝ} (hu : 0 < u) (hsmall : u ≤ 1/10000000000) :
    0 < (millsPoly5 u-1)^2+3*u*millsPoly5 u*(millsPoly5 u-1)+2*u^2*(millsPoly5 u)^3 := by
  have hu1 : u ≤ 1 := by linarith
  have hcoef : 0 < 4-108*u-8199*u^2+30609*u^3-144855*u^4+
      596565*u^5+1137645*u^6+7399350*u^7-11198250*u^8+
      36250200*u^9-142884000*u^10+562605750*u^11-1687817250*u^12 := by
    nlinarith [pow_small hu.le hu1 1, pow_small hu.le hu1 3,
      pow_small hu.le hu1 7, pow_small hu.le hu1 9, pow_small hu.le hu1 11,
      pow_nonneg hu.le 3, pow_nonneg hu.le 5, pow_nonneg hu.le 6,
      pow_nonneg hu.le 7, pow_nonneg hu.le 9, pow_nonneg hu.le 11]
  calc
    0 < u^5*(4-108*u-8199*u^2+30609*u^3-144855*u^4+
      596565*u^5+1137645*u^6+7399350*u^7-11198250*u^8+
      36250200*u^9-142884000*u^10+562605750*u^11-1687817250*u^12) :=
        mul_pos (pow_pos hu 5) hcoef
    _ = (millsPoly5 u-1)^2+3*u*millsPoly5 u*(millsPoly5 u-1)+2*u^2*(millsPoly5 u)^3 := by
      unfold millsPoly5 millsPoly4
      ring

theorem mills_interval_F_pos {u r : ℝ} (hu : 0 < u)
    (hsmall : u ≤ 1/10000000000)
    (hrl : millsPoly5 u ≤ r) (hru : r ≤ millsPoly4 u) :
    0 < (1-u)*r^2-3*r+2 := by
  obtain ⟨hp5, h54, hp4⟩ := millsPoly_bounds hu hsmall
  have hr1 : r ≤ 1 := hru.trans hp4
  have hu1 : u ≤ 1 := by linarith
  have hm := mul_le_mul_of_nonneg_left (add_le_add hr1 hp4) (sub_nonneg.mpr hu1)
  have hb : 0 ≤ 3-(1-u)*(r+millsPoly4 u) := by nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hru) hb
  have he : ((1-u)*r^2-3*r+2)-((1-u)*(millsPoly4 u)^2-3*millsPoly4 u+2) =
      (millsPoly4 u-r)*(3-(1-u)*(r+millsPoly4 u)) := by ring
  rw [← he] at hp
  linarith [mills_F_poly_pos hu hsmall]

theorem mills_interval_D_pos {u r : ℝ} (hu : 0 < u)
    (hsmall : u ≤ 1/10000000000)
    (hrl : millsPoly5 u ≤ r) (hru : r ≤ millsPoly4 u) :
    0 < (r-1)^2+3*u*r*(r-1)+2*u^2*r^3 := by
  obtain ⟨hp5, h54, hp4⟩ := millsPoly_bounds hu hsmall
  have hu1 : u < 1 := by linarith
  have hp50 : 0 ≤ millsPoly5 u := by linarith
  have hr0 : 0 ≤ r := hp50.trans hrl
  have hrlo : 1-u ≤ r := hp5.trans hrl
  have hsum : 1-2*u ≤ r+millsPoly5 u-1 := by linarith
  have hm := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 3*u)
  have hn : 0 ≤ 2*u^2*(r^2+r*millsPoly5 u+(millsPoly5 u)^2) := by positivity
  have hgap : 0 < u*(1-6*u) := mul_pos hu (by linarith)
  have hb : 0 ≤ r+millsPoly5 u-2+3*u*(r+millsPoly5 u-1)+
      2*u^2*(r^2+r*millsPoly5 u+(millsPoly5 u)^2) := by nlinarith
  have hp := mul_nonneg (sub_nonneg.mpr hrl) hb
  have he : ((r-1)^2+3*u*r*(r-1)+2*u^2*r^3) -
      ((millsPoly5 u-1)^2+3*u*millsPoly5 u*(millsPoly5 u-1)+2*u^2*(millsPoly5 u)^3) =
      (r-millsPoly5 u)*(r+millsPoly5 u-2+3*u*(r+millsPoly5 u-1)+
      2*u^2*(r^2+r*millsPoly5 u+(millsPoly5 u)^2)) := by ring
  rw [← he] at hp
  linarith [mills_D_poly_pos hu hsmall]

theorem mills_interval_h_pos {u r : ℝ} (hu : 0 < u)
    (hsmall : u ≤ 1/10000000000) (hru : r ≤ millsPoly4 u) : 0 < 1-r := by
  have hu1 : u ≤ 1 := by linarith
  have hb : 0 < 1-3*u+15*u^2-105*u^3 := by
    nlinarith [pow_small hu.le hu1 2, sq_nonneg u]
  have hp := mul_pos hu hb
  have he : u*(1-3*u+15*u^2-105*u^3) = 1-millsPoly4 u := by
    unfold millsPoly4
    ring
  rw [he] at hp
  linarith

theorem mills_interval_sigma_pos {u r : ℝ} (hu : 0 < u)
    (hsmall : u ≤ 1/10000000000) (hrl : millsPoly5 u ≤ r) :
    0 < u*r^2+r-1 := by
  have hu1 : u ≤ 1 := by linarith
  have hb : 0 < 1-8*u+69*u^2-696*u^3-2190*u^4+2745*u^5-
      8820*u^6+39375*u^7-198450*u^8+893025*u^9 := by
    nlinarith [pow_small hu.le hu1 2, pow_small hu.le hu1 3,
      pow_small hu.le hu1 5, pow_small hu.le hu1 7,
      pow_nonneg hu.le 2, pow_nonneg hu.le 5, pow_nonneg hu.le 7, pow_nonneg hu.le 9]
  have hp := mul_pos (pow_pos hu 2) hb
  have he : u^2*(1-8*u+69*u^2-696*u^3-2190*u^4+2745*u^5-
      8820*u^6+39375*u^7-198450*u^8+893025*u^9) =
      u*(millsPoly5 u)^2+millsPoly5 u-1 := by
    unfold millsPoly5 millsPoly4
    ring
  rw [he] at hp
  have hp50 : 0 ≤ millsPoly5 u := by
    have := (millsPoly_bounds hu hsmall).1
    linarith
  have hr0 : 0 ≤ r := hp50.trans hrl
  have hm := mul_nonneg (sub_nonneg.mpr hrl)
    (by positivity : 0 ≤ 1+u*(r+millsPoly5 u))
  nlinarith
end SimplexFull

