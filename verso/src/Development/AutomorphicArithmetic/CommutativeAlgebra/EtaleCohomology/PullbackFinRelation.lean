import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GalAwayCongr
import GroundTheory.PAdicHodge.FontaineLemmaInvariants
import GroundTheory.PAdicHodge.UnramifiedFrob
import GroundTheory.PAdicHodge.BCrisEigenWitt

set_option maxSynthPendingDepth 1
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison GroundTheory.PAdicHodge

namespace UpperTheory.Ru.crystallineComparison.PBI

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section

set_option backward.isDefEq.respectTransparency false

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem coe_sub_oc (a b : OC l) : ((a - b : OC l) : ℂ_[l]) = (a : ℂ_[l]) - (b : ℂ_[l]) := rfl

/- English proof (translation)
Assume the negation of the conclusion as `h0`. Establish `hu : IsUnit (r.s (r.ρ d))` using `(IsUnit.mk0 _ h0).map r.s`. Establish `h1` using `(IsPerfectoidField.isUnit_iff_norm_untilt (K := ℂ_[l]) l).1 hu`. Establish `h2` using `r.hs d`. Rewrite `h2` using `[coe_sub_oc]`.

Establish `h3 : ‖((PreTilt.untilt (r.s (r.ρ d)) : OC l) : ℂ_[l])‖ < 1`. Establish `e : ((PreTilt.untilt (r.s (r.ρ d)) : OC l) : ℂ_[l]) = (((PreTilt.untilt (r.s (r.ρ d)) : OC l) : ℂ_[l]) - ((okToOC l K d : OC l) : ℂ_[l])) + ((okToOC l K d : OC l) : ℂ_[l])` using `by ring`. Rewrite using `[e]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h2 h)`. Conclude with `absurd h1 h3.ne`.
-/
private theorem rho_zero (r : Res l K) (d : OK l K) (h : ‖((okToOC l K d : OC l) : ℂ_[l])‖ < 1) : r.ρ d = 0 := by
  by_contra h0
  have hu : IsUnit (r.s (r.ρ d)) := (IsUnit.mk0 _ h0).map r.s
  have h1 := (IsPerfectoidField.isUnit_iff_norm_untilt (K := ℂ_[l]) l).1 hu
  have h2 := r.hs d
  rw [coe_sub_oc] at h2
  have h3 : ‖((PreTilt.untilt (r.s (r.ρ d)) : OC l) : ℂ_[l])‖ < 1 := by
    have e : ((PreTilt.untilt (r.s (r.ρ d)) : OC l) : ℂ_[l]) =
        (((PreTilt.untilt (r.s (r.ρ d)) : OC l) : ℂ_[l]) - ((okToOC l K d : OC l) : ℂ_[l])) + ((okToOC l K d : OC l) : ℂ_[l]) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h2 h)
  exact absurd h1 h3.ne

/- English proof (translation)
Take `⟨x, rfl⟩` from `r.surj a`. Establish `hc : ‖((x : K) : PadicAlgCl l)‖ ≤ 1` using `mem_normInteger.1 x.2`. Take `⟨k₀, k₁, hlt, hn⟩` from `exists_lt_norm_pow_sub_lt hc one_pos (fun k => l ^ k)`. Establish `hd` using `rho_zero r (x ^ l ^ k₁ - x ^ l ^ k₀) (by`. Establish `e : ((okToOC l K (x ^ l ^ k₁ - x ^ l ^ k₀) : OC l) : ℂ_[l]) = clToC l (((x : K) : PadicAlgCl l) ^ l ^ k₁ - ((x : K) : PadicAlgCl l) ^ l ^ k₀)`.

Simplify using `[okToOC]`. Rewrite using `[e, norm_clToC]`. Conclude with `hn)`. Rewrite `hd` using `[map_sub, map_pow, map_pow, sub_eq_zero]`. Use `⟨k₁ - k₀, by omega, ?_⟩` and prove the remaining obligations.

Establish `h0 : ((r.ρ x) ^ l ^ (k₁ - k₀) - r.ρ x) ^ l ^ k₀ = 0`. Rewrite using `[sub_pow_char_pow, ← pow_mul, ← pow_add, Nat.sub_add_cancel hlt.le, hd, sub_self]`. Conclude with `sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1 h0)`.
-/
private theorem pow_fix (r : Res l K) (a : r.k) : ∃ f : ℕ, 0 < f ∧ a ^ l ^ f = a := by
  obtain ⟨x, rfl⟩ := r.surj a
  have hc : ‖((x : K) : PadicAlgCl l)‖ ≤ 1 := mem_normInteger.1 x.2
  obtain ⟨k₀, k₁, hlt, hn⟩ := exists_lt_norm_pow_sub_lt hc one_pos (fun k => l ^ k)
  have hd := rho_zero r (x ^ l ^ k₁ - x ^ l ^ k₀) (by
    have e : ((okToOC l K (x ^ l ^ k₁ - x ^ l ^ k₀) : OC l) : ℂ_[l]) =
        clToC l (((x : K) : PadicAlgCl l) ^ l ^ k₁ - ((x : K) : PadicAlgCl l) ^ l ^ k₀) := by
      simp [okToOC]
    rw [e, norm_clToC]
    exact hn)
  rw [map_sub, map_pow, map_pow, sub_eq_zero] at hd
  refine ⟨k₁ - k₀, by omega, ?_⟩
  have h0 : ((r.ρ x) ^ l ^ (k₁ - k₀) - r.ρ x) ^ l ^ k₀ = 0 := by
    rw [sub_pow_char_pow, ← pow_mul, ← pow_add, Nat.sub_add_cancel hlt.le, hd, sub_self]
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1 h0)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, pow_succ, untilt_mul]`. Simplify using `[ih]`.
-/
private theorem untilt_pow' (x : Ob l) (n : ℕ) :
    ((PreTilt.untilt (x ^ n) : OC l) : ℂ_[l]) = ((PreTilt.untilt x : OC l) : ℂ_[l]) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, untilt_mul]; simp [ih]

/- English proof (translation)
Take `⟨f, hf, haf⟩` from `pow_fix r a`. Take `⟨x, rfl⟩` from `r.surj a`. Establish `hq : 1 < l ^ f` using `Nat.one_lt_pow hf.ne' (Fact.out : l.Prime).one_lt`. Establish `hu : (r.s (r.ρ x)) ^ l ^ f = r.s (r.ρ x)` using `by rw [← map_pow, haf]`. Establish `hv : (EigenWitt.galFlat g (r.s (r.ρ x))) ^ l ^ f = EigenWitt.galFlat g (r.s (r.ρ x))`.

Rewrite using `[← map_pow, hu]`. Assume the negation of the conclusion as `hne`. Take `⟨u, hudef⟩ : ∃ u, u = r.s (r.ρ x)` from `⟨_, rfl⟩`. Take `⟨v, hvdef⟩ : ∃ v, v = EigenWitt.galFlat g u` from `⟨_, rfl⟩`. Rewrite `hu`, `hv`, `hne` using `[← hudef]`.

Rewrite `hv`, `hne` using `[← hvdef]`. Establish `he0 : v - u ≠ 0` using `sub_ne_zero.2 hne`. Establish `hee : (v - u) ^ l ^ f = v - u` using `by rw [sub_pow_char_pow, hu, hv]`. Establish `hc : ‖((PreTilt.untilt u : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l])‖ < 1`. Use `r.hs x` as an intermediate fact.

Rewrite `this` using `[coe_sub_oc, ← hudef]`. Conclude with `this`. Establish `hsv : ((PreTilt.untilt v : OC l) : ℂ_[l]) = g • ((PreTilt.untilt u : OC l) : ℂ_[l])`. Rewrite using `[hvdef]`. Conclude with `AInf.coe_untilt_gal g u`.

Establish `hgx : g • ((okToOC l K x : OC l) : ℂ_[l]) = ((okToOC l K x : OC l) : ℂ_[l])` using `congrArg Subtype.val (galOC_okToOC g x)`. Establish `hc' : ‖((PreTilt.untilt v : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l])‖ < 1`. Rewrite using `[hsv, ← hgx, ← smul_sub]`. Establish `h5` using `norm_galCp g (((PreTilt.untilt u : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l]))`. Conclude with `(show ‖g • (((PreTilt.untilt u : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l]))‖ = _ from h5).trans_lt hc`.

Establish `hl : ‖(l : ℂ_[l])‖ < 1` using `norm_natCast_p_lt_one`. Establish `h1` using `norm_untilt_add_sub_le (K := ℂ_[l]) (p := l) (v - u) u`. Rewrite `h1` using `[sub_add_cancel]`. Establish `h2 : ‖((PreTilt.untilt (v - u) : OC l) : ℂ_[l])‖ < 1`. Establish `e : ((PreTilt.untilt (v - u) : OC l) : ℂ_[l]) = (((PreTilt.untilt v : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l])) - (((PreTilt.untilt u : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l])) - (((PreTilt.untilt v : OC l) : ℂ_[l]) - (((PreTilt.untilt (v - u) : OC l) : ℂ_[l]) + …` using `by ring`.

Rewrite using `[e]`. Use `(norm_sub_le_max_of_ultrametric _ _).trans_lt (max_lt ((norm_sub_le_max_of_ultrametric _ _).trans_lt (max_lt hc' hc)) (h1.trans_lt hl))` and prove the remaining obligations. Establish `h3 : ‖((PreTilt.untilt (v - u) : OC l) : ℂ_[l])‖ ^ l ^ f = ‖((PreTilt.untilt (v - u) : OC l) : ℂ_[l])‖`. Rewrite using `[← norm_pow, ← untilt_pow', hee]`. Establish `h4 : 0 < ‖((PreTilt.untilt (v - u) : OC l) : ℂ_[l])‖`.

Use `norm_pos_iff.2 fun h => he0 ((IsPerfectoidField.untilt_eq_zero_iff (K := ℂ_[l]) l).1 (Subtype.ext h))` and prove the remaining obligations. Conclude with `absurd h3 (pow_lt_self_of_lt_one₀ h4 h2 hq).ne`.
-/
private theorem gfix (r : Res l K) (g : Gal(PadicAlgCl l/K)) (a : r.k) : EigenWitt.galFlat g (r.s a) = r.s a := by
  obtain ⟨f, hf, haf⟩ := pow_fix r a
  obtain ⟨x, rfl⟩ := r.surj a
  have hq : 1 < l ^ f := Nat.one_lt_pow hf.ne' (Fact.out : l.Prime).one_lt
  have hu : (r.s (r.ρ x)) ^ l ^ f = r.s (r.ρ x) := by rw [← map_pow, haf]
  have hv : (EigenWitt.galFlat g (r.s (r.ρ x))) ^ l ^ f = EigenWitt.galFlat g (r.s (r.ρ x)) := by
    rw [← map_pow, hu]
  by_contra hne
  obtain ⟨u, hudef⟩ : ∃ u, u = r.s (r.ρ x) := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v, v = EigenWitt.galFlat g u := ⟨_, rfl⟩
  rw [← hudef] at hu hv hne
  rw [← hvdef] at hv hne
  have he0 : v - u ≠ 0 := sub_ne_zero.2 hne
  have hee : (v - u) ^ l ^ f = v - u := by rw [sub_pow_char_pow, hu, hv]
  have hc : ‖((PreTilt.untilt u : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l])‖ < 1 := by
    have := r.hs x
    rw [coe_sub_oc, ← hudef] at this
    exact this
  have hsv : ((PreTilt.untilt v : OC l) : ℂ_[l]) = g • ((PreTilt.untilt u : OC l) : ℂ_[l]) := by
    rw [hvdef]; exact AInf.coe_untilt_gal g u
  have hgx : g • ((okToOC l K x : OC l) : ℂ_[l]) = ((okToOC l K x : OC l) : ℂ_[l]) :=
    congrArg Subtype.val (galOC_okToOC g x)
  have hc' : ‖((PreTilt.untilt v : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l])‖ < 1 := by
    rw [hsv, ← hgx, ← smul_sub]
    have h5 := norm_galCp g (((PreTilt.untilt u : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l]))
    exact (show ‖g • (((PreTilt.untilt u : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l]))‖ = _ from h5).trans_lt hc
  have hl : ‖(l : ℂ_[l])‖ < 1 := norm_natCast_p_lt_one
  have h1 := norm_untilt_add_sub_le (K := ℂ_[l]) (p := l) (v - u) u
  rw [sub_add_cancel] at h1
  have h2 : ‖((PreTilt.untilt (v - u) : OC l) : ℂ_[l])‖ < 1 := by
    have e : ((PreTilt.untilt (v - u) : OC l) : ℂ_[l]) =
        (((PreTilt.untilt v : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l])) -
        (((PreTilt.untilt u : OC l) : ℂ_[l]) - ((okToOC l K x : OC l) : ℂ_[l])) -
        (((PreTilt.untilt v : OC l) : ℂ_[l]) - (((PreTilt.untilt (v - u) : OC l) : ℂ_[l]) + ((PreTilt.untilt u : OC l) : ℂ_[l]))) := by ring
    rw [e]
    refine (norm_sub_le_max_of_ultrametric _ _).trans_lt (max_lt ((norm_sub_le_max_of_ultrametric _ _).trans_lt (max_lt hc' hc)) (h1.trans_lt hl))
  have h3 : ‖((PreTilt.untilt (v - u) : OC l) : ℂ_[l])‖ ^ l ^ f = ‖((PreTilt.untilt (v - u) : OC l) : ℂ_[l])‖ := by
    rw [← norm_pow, ← untilt_pow', hee]
  have h4 : 0 < ‖((PreTilt.untilt (v - u) : OC l) : ℂ_[l])‖ := by
    refine norm_pos_iff.2 fun h => he0 ((IsPerfectoidField.untilt_eq_zero_iff (K := ℂ_[l]) l).1 (Subtype.ext h))
  exact absurd h3 (pow_lt_self_of_lt_one₀ h4 h2 hq).ne

/- English proof (translation)
Establish `hs : ∀ x : Z, ∃ (a : k) (x' : Z), (x : OC l) = τ (WittVector.teichmuller l a) + (l : OC l) * x'` using `fun x => by`. Take `⟨a, x', h, e⟩` from `hstep x x.2`. Conclude with `⟨a, ⟨x', h⟩, e⟩`. Use `choose A N hAN using hs`. Set `E : Z → WittVector l k` to `fun x => WittVector.mk l (fun i => A (N^[i] x) ^ l ^ i)`.

Establish `hcoeff : ∀ x i, (E x).coeff i = A (N^[i] x) ^ l ^ i` using `fun x i => rfl`. Establish `hE : ∀ x, E x = WittVector.teichmuller l (A x) + (l : WittVector l k) * E (N x)`. Introduce `x`. Rewrite using `[mul_comm (l : WittVector l k), ← WittVector.verschiebung_frobenius]`. Use extensionality with `n`.

Rewrite using `[WittVector.coeff_add_of_disjoint]`. Consider the cases of `n with`. Consider the case `zero => simp [hcoeff, WittVector.teichmuller_coeff_zero]`. Consider the case `succ n`. Rewrite using `[WittVector.teichmuller_coeff_pos _ _ _ (Nat.succ_pos n), WittVector.verschiebung_coeff_succ, WittVector.coeff_frobenius_charP, hcoeff, hcoeff, zero_add, Function.iterate_succ_apply, pow_succ, pow_mul]`.

Introduce `n`. Consider the cases of `n with`. Consider the case `zero => right`. Simplify using the standard rewrite rules. Consider the case `succ n => left`.

Conclude with `WittVector.teichmuller_coeff_pos _ _ _ (Nat.succ_pos n)`. Establish `hdiv : ∀ (n : ℕ) (x : Z), ∃ y : OC l, (x : OC l) - τ (E x) = (l : OC l) ^ n * y`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact fun x => ⟨(x : OC l) - τ (E x), by simp⟩`.

Consider the case `succ n ih`. Introduce `x`. Take `⟨y, hy⟩` from `ih (N x)`. Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `h1` using `hAN x`.

Establish `h2 : τ (E x) = τ (WittVector.teichmuller l (A x)) + (l : OC l) * τ (E (N x))` using `by conv_lhs => rw [hE x]`. Rewrite using `[map_add, map_mul, map_natCast]`. Rewrite using `[h2, h1, pow_succ']`. Take the linear combination `(l : OC l) * hy`. Introduce `x hx`.

Use `⟨E ⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖((x - τ (E ⟨x, hx⟩) : OC l) : ℂ_[l])‖` using `norm_pos_iff.2 fun h => hne (sub_eq_zero.1 (Subtype.ext h)).symm`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one hpos (norm_natCast_p_lt_one (p := l))`. Take `⟨y, hy⟩` from `hdiv n ⟨x, hx⟩`.

Establish `h1 : ‖((x - τ (E ⟨x, hx⟩) : OC l) : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ n`. Establish `hy' : x - τ (E ⟨x, hx⟩) = (l : OC l) ^ n * y` using `hy`. Rewrite using `[hy']`. Establish `e : (((l : OC l) ^ n * y : OC l) : ℂ_[l]) = (l : ℂ_[l]) ^ n * (y : ℂ_[l])` using `by simp`. Rewrite using `[e, norm_mul, norm_pow]`.

Conclude with `mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (mem_normInteger.1 y.2)`. Conclude with `absurd h1 (not_le.2 hn)`.
-/
private theorem wexp {k : Type} [Field k] [CharP k l] [PerfectRing k l] (τ : WittVector l k →+* OC l) (Z : Set (OC l))
    (hstep : ∀ x ∈ Z, ∃ (a : k) (x' : OC l), x' ∈ Z ∧ x = τ (WittVector.teichmuller l a) + (l : OC l) * x') :
    ∀ x ∈ Z, ∃ w, τ w = x := by
  have hs : ∀ x : Z, ∃ (a : k) (x' : Z), (x : OC l) = τ (WittVector.teichmuller l a) + (l : OC l) * x' := fun x => by
    obtain ⟨a, x', h, e⟩ := hstep x x.2
    exact ⟨a, ⟨x', h⟩, e⟩
  choose A N hAN using hs
  let E : Z → WittVector l k := fun x => WittVector.mk l (fun i => A (N^[i] x) ^ l ^ i)
  have hcoeff : ∀ x i, (E x).coeff i = A (N^[i] x) ^ l ^ i := fun x i => rfl
  have hE : ∀ x, E x = WittVector.teichmuller l (A x) + (l : WittVector l k) * E (N x) := by
    intro x
    rw [mul_comm (l : WittVector l k), ← WittVector.verschiebung_frobenius]
    ext n
    rw [WittVector.coeff_add_of_disjoint]
    · cases n with
      | zero => simp [hcoeff, WittVector.teichmuller_coeff_zero]
      | succ n =>
        rw [WittVector.teichmuller_coeff_pos _ _ _ (Nat.succ_pos n), WittVector.verschiebung_coeff_succ,
          WittVector.coeff_frobenius_charP, hcoeff, hcoeff, zero_add, Function.iterate_succ_apply, pow_succ, pow_mul]
    · intro n
      cases n with
      | zero => right; simp
      | succ n => left; exact WittVector.teichmuller_coeff_pos _ _ _ (Nat.succ_pos n)
  have hdiv : ∀ (n : ℕ) (x : Z), ∃ y : OC l, (x : OC l) - τ (E x) = (l : OC l) ^ n * y := by
    intro n
    induction n with
    | zero => exact fun x => ⟨(x : OC l) - τ (E x), by simp⟩
    | succ n ih =>
      intro x
      obtain ⟨y, hy⟩ := ih (N x)
      refine ⟨y, ?_⟩
      have h1 := hAN x
      have h2 : τ (E x) = τ (WittVector.teichmuller l (A x)) + (l : OC l) * τ (E (N x)) := by
        conv_lhs => rw [hE x]
        rw [map_add, map_mul, map_natCast]
      rw [h2, h1, pow_succ']
      linear_combination (l : OC l) * hy
  intro x hx
  refine ⟨E ⟨x, hx⟩, ?_⟩
  by_contra hne
  have hpos : 0 < ‖((x - τ (E ⟨x, hx⟩) : OC l) : ℂ_[l])‖ :=
    norm_pos_iff.2 fun h => hne (sub_eq_zero.1 (Subtype.ext h)).symm
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (norm_natCast_p_lt_one (p := l))
  obtain ⟨y, hy⟩ := hdiv n ⟨x, hx⟩
  have h1 : ‖((x - τ (E ⟨x, hx⟩) : OC l) : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ n := by
    have hy' : x - τ (E ⟨x, hx⟩) = (l : OC l) ^ n * y := hy
    rw [hy']
    have e : (((l : OC l) ^ n * y : OC l) : ℂ_[l]) = (l : ℂ_[l]) ^ n * (y : ℂ_[l]) := by simp
    rw [e, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (mem_normInteger.1 y.2)
  exact absurd h1 (not_le.2 hn)

end

local notation "hE" => (untilt_epsilon (p := l))
local notation "hZ" => (untilt_frobeniusEquiv_symm_epsilon_ne_one (p := l))

variable (l) in
private def fB : Acris l →+* ACris.BCris (untilt_epsilon (p := l)) :=
  (algebraMap (ACris.BCrisPlus ℂ_[l] l) (ACris.BCris (untilt_epsilon (p := l)))).comp
    (algebraMap (Acris l) (ACris.BCrisPlus ℂ_[l] l))

/- English proof (translation)
Express the relevant statement in the definitionally equal form `ACris.iotaB hE hZ (algebraMap (ACris.BCrisPlus ℂ_[l] l) _ (algebraMap (Acris l) _ a)) = _`. Rewrite using `[ACris.iotaB_algebraMap, ACris.iotaPlus_algebraMap]`. Both sides reduce to the same expression.
-/
private theorem iB_fB (a : Acris l) : ACris.iotaB hE hZ (fB l a) = DeRhamPotentiallySemistable.DRPst.iC l a := by
  change ACris.iotaB hE hZ (algebraMap (ACris.BCrisPlus ℂ_[l] l) _ (algebraMap (Acris l) _ a)) = _
  rw [ACris.iotaB_algebraMap, ACris.iotaPlus_algebraMap]
  rfl

/- English proof (translation)
The claim follows from `(IsFractionRing.injective (BDeRhamPlus (normInteger ℂ_[l]) l) (BDeRham (normInteger ℂ_[l]) l)).comp (ACris.iota_injective (K := ℂ_[l]) (p := l))`.
-/
private theorem iC_inj : Function.Injective (DeRhamPotentiallySemistable.DRPst.iC l) :=
  (IsFractionRing.injective (BDeRhamPlus (normInteger ℂ_[l]) l) (BDeRham (normInteger ℂ_[l]) l)).comp
    (ACris.iota_injective (K := ℂ_[l]) (p := l))

/- English proof (translation)
The claim follows from `IsLocalization.Away.algebraMap_isUnit (S := ACris.BCris (untilt_epsilon (p := l))) (algebraMap (ACris.ACris ℂ_[l] l) (ACris.BCrisPlus ℂ_[l] l) (ACris.periodT (untilt_epsilon (p := l))))`.
-/
private theorem fB_t_unit : IsUnit (fB l (tA l)) :=
  IsLocalization.Away.algebraMap_isUnit (S := ACris.BCris (untilt_epsilon (p := l)))
    (algebraMap (ACris.ACris ℂ_[l] l) (ACris.BCrisPlus ℂ_[l] l) (ACris.periodT (untilt_epsilon (p := l))))

/- English proof (translation)
Rewrite using `[← iB_fB]`. Conclude with `fB_t_unit.map _`.
-/
private theorem iC_t_unit : IsUnit (DeRhamPotentiallySemistable.DRPst.iC l (tA l)) := by
  rw [← iB_fB]
  exact fB_t_unit.map _

/- English proof (translation)
Express the relevant statement in the definitionally equal form `ACris.galB hE σ (algebraMap (ACris.BCrisPlus ℂ_[l] l) _ (algebraMap (Acris l) _ a)) = _`. Rewrite using `[ACris.galB_algebraMap]`. Conclude with `congrArg _ (ACris.galPlus_algebraMap σ a)`.
-/
private theorem galB_fB (σ : Gal(PadicAlgCl l/K)) (a : Acris l) :
    ACris.galB hE σ (fB l a) = fB l (ACris.galCris σ a) := by
  change ACris.galB hE σ (algebraMap (ACris.BCrisPlus ℂ_[l] l) _ (algebraMap (Acris l) _ a)) = _
  rw [ACris.galB_algebraMap]
  exact congrArg _ (ACris.galPlus_algebraMap σ a)

/- English proof (translation)
Establish `h : σ • (WittVector.map r.s w) = WittVector.map r.s w`. Use extensionality with `n`. Rewrite using `[AInf.gal_smul_coeff, WittVector.map_coeff]`. Conclude with `gfix r σ _`. Establish `h2` using `ACris.gal_smul_algebraMap σ (WittVector.map r.s w)`.

Rewrite `h2` using `[h]`. Conclude with `h2`.
-/
private theorem galCris_w (r : Res l K) (σ : Gal(PadicAlgCl l/K)) (w : WittVector l r.k) :
    ACris.galCris σ (r.w w) = r.w w := by
  have h : σ • (WittVector.map r.s w) = WittVector.map r.s w := by
    ext n
    rw [AInf.gal_smul_coeff, WittVector.map_coeff]
    exact gfix r σ _
  have h2 := ACris.gal_smul_algebraMap σ (WittVector.map r.s w)
  rw [h] at h2
  exact h2

private def tau (r : Res l K) : WittVector l r.k →+* OC l :=
  (WittVector.fontaineTheta (OC l) l).comp (WittVector.map r.s)

/- English proof (translation)
Rewrite using `[tau, RingHom.comp_apply, WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller]`.
-/
private theorem tau_teich (r : Res l K) (a : r.k) :
    tau r (WittVector.teichmuller l a) = PreTilt.untilt (r.s a) := by
  rw [tau, RingHom.comp_apply, WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller]

/- English proof (translation)
Take `⟨k, hk, h⟩` from `ACris.bCris_fixed_mem_maxUnramified hE hZ (K := K) (fB l (r.w w)) (fun σ => by`. Rewrite using `[galB_fB, galCris_w])`. Rewrite `h` using `[iB_fB]`. Use `⟨k, hk, h, ?_⟩` and prove the remaining obligations. Establish `h1 : ACris.iota ℂ_[l] l (r.w w) = algClToBdR l k` using `IsFractionRing.injective (BDeRhamPlus (normInteger ℂ_[l]) l) (BDeRham (normInteger ℂ_[l]) l) h`.

Establish `h2` using `congrArg (thetaAlgHom l) h1`. Rewrite `h2` using `[thetaAlgHom_algClToBdR]`. Establish `h3 : r.w w = algebraMap (Ainf l) (Acris l) (WittVector.map r.s w)` using `rfl`. Rewrite `h2` using `[h3, ACris.iota_algebraMap]`. Establish `h4 : thetaAlgHom l (wittToBDeRhamPlus (normInteger ℂ_[l]) l (WittVector.map r.s w)) = ((tau r w : OC l) : ℂ_[l])` using `IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus l (WittVector.map r.s w)`.

Conclude with `h2.symm.trans h4`.
-/
private theorem hT [FiniteDimensional ℚ_[l] K] (r : Res l K) (w : WittVector l r.k) :
    ∃ k ∈ maxUnramified l K,
      DeRhamPotentiallySemistable.DRPst.iC l (r.w w) = algebraMap (BDeRhamPlus (normInteger ℂ_[l]) l) (BDeRham (normInteger ℂ_[l]) l) (algClToBdR l k) ∧
      clToC l k = ((tau r w : OC l) : ℂ_[l]) := by
  obtain ⟨k, hk, h⟩ := ACris.bCris_fixed_mem_maxUnramified hE hZ (K := K) (fB l (r.w w)) (fun σ => by
    rw [galB_fB, galCris_w])
  rw [iB_fB] at h
  refine ⟨k, hk, h, ?_⟩
  have h1 : ACris.iota ℂ_[l] l (r.w w) = algClToBdR l k :=
    IsFractionRing.injective (BDeRhamPlus (normInteger ℂ_[l]) l) (BDeRham (normInteger ℂ_[l]) l) h
  have h2 := congrArg (thetaAlgHom l) h1
  rw [thetaAlgHom_algClToBdR] at h2
  have h3 : r.w w = algebraMap (Ainf l) (Acris l) (WittVector.map r.s w) := rfl
  rw [h3, ACris.iota_algebraMap] at h2
  have h4 : thetaAlgHom l (wittToBDeRhamPlus (normInteger ℂ_[l]) l (WittVector.map r.s w)) = ((tau r w : OC l) : ℂ_[l]) :=
    IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus l (WittVector.map r.s w)
  exact h2.symm.trans h4

/- English proof (translation)
Establish `h1 : i a = q k * i t ^ n`. Rewrite using `[← hk, ← hji a, ← hji t, ← map_pow, ← map_mul, mul_assoc, ← mul_pow, mul_comm T, hT, one_pow, mul_one]`. Rewrite using `[map_mul, map_mul, map_pow, map_pow, map_natCast, hW, h1, map_mul, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem pullback_fin_relation {A F D P : Type*} [CommRing A] [CommRing F] [CommRing D] [CommRing P] (f : A →+* F) (j : F →+* D)
    (i : A →+* D) (q : P →+* D) (hji : ∀ u, j (f u) = i u) {t a W : A} {T : F} {n e L : ℕ} {k : P}
    (hT : f t * T = 1) (hk : j (f a * T ^ n) = q k) (hW : i W = q ((L : P) ^ e * k)) :
    i ((L : A) ^ e * a) = i (t ^ n * W) := by
  have h1 : i a = q k * i t ^ n := by
    rw [← hk, ← hji a, ← hji t, ← map_pow, ← map_mul, mul_assoc, ← mul_pow, mul_comm T, hT, one_pow, mul_one]
  rw [map_mul, map_mul, map_pow, map_pow, map_natCast, hW, h1, map_mul, map_pow, map_natCast]
  ring

/- English proof (translation)
Apply `ut.mul_left_cancel` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem fin2 {A C : Type*} [CommRing A] [CommRing C] (c : A →+* C) {t a W : A} {x : C} {n e L : ℕ}
    (ut : IsUnit (c t ^ n)) (hna : c t ^ n * x = c a) (hA : (L : A) ^ e * a = t ^ n * W) :
    (L : C) ^ e * x = c W := by
  apply ut.mul_left_cancel
  calc c t ^ n * ((L : C) ^ e * x) = (L : C) ^ e * (c t ^ n * x) := by ring
    _ = c ((L : A) ^ e * a) := by rw [hna, map_mul, map_pow, map_natCast]
    _ = c (t ^ n * W) := by rw [hA]
    _ = c t ^ n * c W := by rw [map_mul, map_pow]

/- English proof (translation)
Establish `hs : f (s t) * G T = 1`. Rewrite using `[← hG, ← map_mul, hT, map_one]`. Establish `I2` using `congrArg f I1`. Simplify using `only [map_mul, map_pow] at I2`. Rewrite using `[map_mul, map_pow, hG]`.

Combine the equalities or inequalities in the displayed calculation.
-/
private theorem fix_aux {A F : Type*} [CommRing A] [CommRing F] (f : A →+* F) (G : F →+* F) (s : A →+* A)
    {t a : A} {T : F} {n : ℕ} (hG : ∀ u, G (f u) = f (s u)) (hT : f t * T = 1)
    (I1 : s a * t ^ n = a * s t ^ n) : G (f a * T ^ n) = f a * T ^ n := by
  have hs : f (s t) * G T = 1 := by
    rw [← hG, ← map_mul, hT, map_one]
  have I2 := congrArg f I1
  simp only [map_mul, map_pow] at I2
  rw [map_mul, map_pow, hG]
  calc f (s a) * G T ^ n = f (s a) * G T ^ n * (f t * T) ^ n := by rw [hT, one_pow, mul_one]
    _ = (f (s a) * f t ^ n) * (G T ^ n * T ^ n) := by rw [mul_pow]; ring
    _ = f a * f (s t) ^ n * (G T ^ n * T ^ n) := by rw [I2]
    _ = f a * T ^ n * (f (s t) * G T) ^ n := by rw [mul_pow]; ring
    _ = f a * T ^ n := by rw [hs, one_pow, mul_one]

/- English proof (translation)
Set `Z : Set (OC l)` to `{x | ∃ k ∈ maxUnramified l K, (x : ℂ_[l]) = clToC l k}`. Establish `hstep : ∀ x ∈ Z, ∃ (a : r.k) (x' : OC l), x' ∈ Z ∧ x = tau r (WittVector.teichmuller l a) + (l : OC l) * x'`. Introduce and unpack `x ⟨k, hk, hx⟩`. Establish `hk1 : ‖k‖ ≤ 1`. Rewrite using `[← norm_clToC, ← hx]`.

Conclude with `mem_normInteger.1 x.2`. Establish `hkK : k ∈ K` using `(mem_maxUnramified.1 hk).1`. Set `xo : OK l K` to `⟨⟨k, hkK⟩, mem_normInteger.2 hk1⟩`. Take `⟨k₀, hk₀, -, hk₀τ⟩` from `hT r (WittVector.teichmuller l (r.ρ xo))`. Rewrite `hk₀τ` using `[tau_teich]`.

Establish `hlt : ‖k - k₀‖ < 1`. Establish `h2` using `r.hs xo`. Rewrite `h2` using `[coe_sub_oc, ← hk₀τ]`. Establish `e : ((okToOC l K xo : OC l) : ℂ_[l]) = clToC l k` using `rfl`. Rewrite `h2` using `[e, ← map_sub, norm_clToC, norm_sub_rev]`.

Conclude with `h2`. Establish `hy : k - k₀ ∈ maxUnramified l K` using `sub_mem hk hk₀`. Establish `hl0 : (l : PadicAlgCl l) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`. Establish `hy' : (k - k₀) / (l : PadicAlgCl l) ∈ maxUnramified l K` using `div_mem hy (natCast_mem _ l)`. Establish `hn : ‖(k - k₀) / (l : PadicAlgCl l)‖ ≤ 1`.

Distinguish the cases in `h0 : k - k₀ = 0`. Simplify using `[h0]`. Take `⟨D, hD⟩` from `ACris.exists_norm_eq_zpow_maxUnramified (K := K) (x := ⟨k - k₀, hy⟩) (fun h => h0 (congrArg Subtype.val h))`. Establish `hD' : ‖k - k₀‖ = ‖(l : PadicAlgCl l)‖ ^ D` using `hD`. Establish `hlpos` using `ACris.norm_p_algCl_pos (p := l)`.

Establish `hl1 : ‖(l : PadicAlgCl l)‖ < 1` using `norm_natCast_p_algCl_lt_one`. Establish `hD1 : 1 ≤ D`. Assume the negation of the conclusion as `hcon`. Establish `h3 : D ≤ 0` using `by omega`. Establish `h4 : 1 ≤ ‖(l : PadicAlgCl l)‖ ^ D` using `one_le_zpow_of_nonpos₀ hlpos hl1.le h3`.

Rewrite `hlt` using `[hD']`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[norm_div, hD', div_le_one hlpos]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨r.ρ xo, ⟨clToC l ((k - k₀) / (l : PadicAlgCl l)), mem_normInteger.2 (by rw [norm_clToC]; exact hn)⟩, ⟨_, hy', rfl⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[tau_teich]`. Express the relevant statement in the definitionally equal form `(x : ℂ_[l]) = ((PreTilt.untilt (r.s (r.ρ xo)) : OC l) : ℂ_[l]) + (l : ℂ_[l]) * clToC l ((k - k₀) / (l : PadicAlgCl l))`. Rewrite using `[hx, ← hk₀τ, ← map_natCast (clToC l) l, ← map_mul, ← map_add]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hx : (⟨clToC l k, mem_normInteger.2 (by rw [norm_clToC]; exact h1)⟩ : OC l) ∈ Z` using `⟨k, hk, rfl⟩`. Take `⟨w, hw⟩` from `wexp (tau r) Z hstep _ hx`. Take `⟨k₁, -, h2, h3⟩` from `hT r w`.

Rewrite `h3` using `[hw]`. Establish `e : k₁ = k` using `(clToC l).injective h3`. Conclude with `⟨w, e ▸ h2⟩`.
-/
private theorem hK [FiniteDimensional ℚ_[l] K] (r : Res l K) {k : PadicAlgCl l} (hk : k ∈ maxUnramified l K) (h1 : ‖k‖ ≤ 1) :
    ∃ w : WittVector l r.k, DeRhamPotentiallySemistable.DRPst.iC l (r.w w) =
      algebraMap (BDeRhamPlus (normInteger ℂ_[l]) l) (BDeRham (normInteger ℂ_[l]) l) (algClToBdR l k) := by
  let Z : Set (OC l) := {x | ∃ k ∈ maxUnramified l K, (x : ℂ_[l]) = clToC l k}
  have hstep : ∀ x ∈ Z, ∃ (a : r.k) (x' : OC l), x' ∈ Z ∧
      x = tau r (WittVector.teichmuller l a) + (l : OC l) * x' := by
    rintro x ⟨k, hk, hx⟩
    have hk1 : ‖k‖ ≤ 1 := by
      rw [← norm_clToC, ← hx]
      exact mem_normInteger.1 x.2
    have hkK : k ∈ K := (mem_maxUnramified.1 hk).1
    let xo : OK l K := ⟨⟨k, hkK⟩, mem_normInteger.2 hk1⟩
    obtain ⟨k₀, hk₀, -, hk₀τ⟩ := hT r (WittVector.teichmuller l (r.ρ xo))
    rw [tau_teich] at hk₀τ
    have hlt : ‖k - k₀‖ < 1 := by
      have h2 := r.hs xo
      rw [coe_sub_oc, ← hk₀τ] at h2
      have e : ((okToOC l K xo : OC l) : ℂ_[l]) = clToC l k := rfl
      rw [e, ← map_sub, norm_clToC, norm_sub_rev] at h2
      exact h2
    have hy : k - k₀ ∈ maxUnramified l K := sub_mem hk hk₀
    have hl0 : (l : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
    have hy' : (k - k₀) / (l : PadicAlgCl l) ∈ maxUnramified l K := div_mem hy (natCast_mem _ l)
    have hn : ‖(k - k₀) / (l : PadicAlgCl l)‖ ≤ 1 := by
      by_cases h0 : k - k₀ = 0
      · simp [h0]
      obtain ⟨D, hD⟩ := ACris.exists_norm_eq_zpow_maxUnramified (K := K) (x := ⟨k - k₀, hy⟩)
        (fun h => h0 (congrArg Subtype.val h))
      have hD' : ‖k - k₀‖ = ‖(l : PadicAlgCl l)‖ ^ D := hD
      have hlpos := ACris.norm_p_algCl_pos (p := l)
      have hl1 : ‖(l : PadicAlgCl l)‖ < 1 := norm_natCast_p_algCl_lt_one
      have hD1 : 1 ≤ D := by
        by_contra hcon
        have h3 : D ≤ 0 := by omega
        have h4 : 1 ≤ ‖(l : PadicAlgCl l)‖ ^ D := one_le_zpow_of_nonpos₀ hlpos hl1.le h3
        rw [hD'] at hlt
        linarith
      rw [norm_div, hD', div_le_one hlpos]
      calc ‖(l : PadicAlgCl l)‖ ^ D ≤ ‖(l : PadicAlgCl l)‖ ^ (1 : ℤ) :=
            zpow_le_zpow_right_of_le_one₀ hlpos hl1.le hD1
        _ = ‖(l : PadicAlgCl l)‖ := zpow_one _
    refine ⟨r.ρ xo, ⟨clToC l ((k - k₀) / (l : PadicAlgCl l)), mem_normInteger.2 (by rw [norm_clToC]; exact hn)⟩,
      ⟨_, hy', rfl⟩, ?_⟩
    apply Subtype.ext
    rw [tau_teich]
    change (x : ℂ_[l]) = ((PreTilt.untilt (r.s (r.ρ xo)) : OC l) : ℂ_[l]) +
      (l : ℂ_[l]) * clToC l ((k - k₀) / (l : PadicAlgCl l))
    rw [hx, ← hk₀τ, ← map_natCast (clToC l) l, ← map_mul, ← map_add]
    congr 1
    field_simp
    ring
  have hx : (⟨clToC l k, mem_normInteger.2 (by rw [norm_clToC]; exact h1)⟩ : OC l) ∈ Z := ⟨k, hk, rfl⟩
  obtain ⟨w, hw⟩ := wexp (tau r) Z hstep _ hx
  obtain ⟨k₁, -, h2, h3⟩ := hT r w
  rw [hw] at h3
  have e : k₁ = k := (clToC l).injective h3
  exact ⟨w, e ▸ h2⟩

/- English proof (translation)
Use `⟨fun g w => galCris_w r _ w, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hcinj : ∀ u v : Acris l, B₀.c u = B₀.c v → u = v`. Introduce `u v h`. Take `⟨m, hm⟩` from `B₀.ker (u - v) (by rw [map_sub, h, sub_self])`. Establish `h1` using `congrArg (DeRhamPotentiallySemistable.DRPst.iC l) hm`.

Rewrite `h1` using `[map_mul, map_pow, map_zero]`. Establish `h2` using `((iC_t_unit.pow m).mul_right_eq_zero).1 h1`. Rewrite `h2` using `[map_sub, sub_eq_zero]`. Conclude with `iC_inj h2`. Take `⟨n, a, hna⟩` from `B₀.loc x`.

Take `⟨T, hT1⟩` from `fB_t_unit (l := l) |>.exists_right_inv`. Establish `hy : ∀ σ : Gal(PadicAlgCl l/K), ACris.galB hE σ (fB l a * T ^ n) = fB l a * T ^ n`. Introduce `σ`. Establish `hσ : IntermediateField.fixingSubgroupEquiv K ((IntermediateField.fixingSubgroupEquiv K).symm σ) = σ` using `MulEquiv.apply_symm_apply _ σ`. Establish `hsc : ∀ u, B₀.σ ((IntermediateField.fixingSubgroupEquiv K).symm σ) (B₀.c u) = B₀.c (ACris.galCris σ u)`.

Introduce `u`. Rewrite using `[B₀.σ_c, galA, hσ]`. Establish `hg` using `hx ((IntermediateField.fixingSubgroupEquiv K).symm σ)`. Use `fix_aux (fB l) (ACris.galB hE σ) (ACris.galCris σ) (galB_fB σ) hT1 (hcinj _ _ ?_)` and prove the remaining obligations. Establish `h1` using `congrArg (B₀.σ ((IntermediateField.fixingSubgroupEquiv K).symm σ)) hna`.

Rewrite `h1` using `[map_mul, map_pow, hg, hsc, hsc]`. Rewrite using `[map_mul, map_mul, map_pow, map_pow, ← h1, ← hna]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨k, hk, hky⟩` from `ACris.bCris_fixed_mem_maxUnramified hE hZ (K := K) _ hy`. Choose the witnesses or unpack the hypotheses as in `⟨e, he⟩ : ∃ e : ℕ, ‖(l : PadicAlgCl l) ^ e * k‖ ≤ 1 := by`.

Establish `hl1 : ‖(l : PadicAlgCl l)‖ < 1` using `norm_natCast_p_algCl_lt_one`. Take `⟨e, he⟩` from `exists_pow_lt_of_lt_one (show 0 < (‖k‖ + 1)⁻¹ by positivity) hl1`. Use `⟨e, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`. Establish `h1 : 0 < ‖k‖ + 1` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨w, hw⟩` from `hK r (mul_mem (pow_mem (natCast_mem _ l) e) hk) he`. Use `⟨e, w, ?_⟩` and prove the remaining obligations. Establish `hA : (l : Acris l) ^ e * a = tA l ^ n * r.w w` using `iC_inj (pullback_fin_relation (fB l) (ACris.iotaB hE hZ) (DeRhamPotentiallySemistable.DRPst.iC l) ((algebraMap (BDeRhamPlus (normInteger ℂ_[l]) l) (BDeRham (normInteger ℂ_[l]) l)).comp (algClToBdR l : PadicAlgCl l →+* BDeRhamPlus (normInteger ℂ_[l]) l)) iB_fB hT1 hky hw)`. Conclude with `fin2 B₀.c (B₀.t_unit.pow n) hna hA`.
-/
private theorem mainC [FiniteDimensional ℚ_[l] K] (B₀ : PB l K) (r : Res l K) : InvC B₀ r := by
  refine ⟨fun g w => galCris_w r _ w, fun x hx => ?_⟩
  have hcinj : ∀ u v : Acris l, B₀.c u = B₀.c v → u = v := by
    intro u v h
    obtain ⟨m, hm⟩ := B₀.ker (u - v) (by rw [map_sub, h, sub_self])
    have h1 := congrArg (DeRhamPotentiallySemistable.DRPst.iC l) hm
    rw [map_mul, map_pow, map_zero] at h1
    have h2 := ((iC_t_unit.pow m).mul_right_eq_zero).1 h1
    rw [map_sub, sub_eq_zero] at h2
    exact iC_inj h2
  obtain ⟨n, a, hna⟩ := B₀.loc x
  obtain ⟨T, hT1⟩ := fB_t_unit (l := l) |>.exists_right_inv
  have hy : ∀ σ : Gal(PadicAlgCl l/K), ACris.galB hE σ (fB l a * T ^ n) = fB l a * T ^ n := by
    intro σ
    have hσ : IntermediateField.fixingSubgroupEquiv K ((IntermediateField.fixingSubgroupEquiv K).symm σ) = σ :=
      MulEquiv.apply_symm_apply _ σ
    have hsc : ∀ u, B₀.σ ((IntermediateField.fixingSubgroupEquiv K).symm σ) (B₀.c u) = B₀.c (ACris.galCris σ u) := by
      intro u
      rw [B₀.σ_c, galA, hσ]
    have hg := hx ((IntermediateField.fixingSubgroupEquiv K).symm σ)
    refine fix_aux (fB l) (ACris.galB hE σ) (ACris.galCris σ) (galB_fB σ) hT1 (hcinj _ _ ?_)
    have h1 := congrArg (B₀.σ ((IntermediateField.fixingSubgroupEquiv K).symm σ)) hna
    rw [map_mul, map_pow, hg, hsc, hsc] at h1
    rw [map_mul, map_mul, map_pow, map_pow, ← h1, ← hna]
    ring
  obtain ⟨k, hk, hky⟩ := ACris.bCris_fixed_mem_maxUnramified hE hZ (K := K) _ hy
  obtain ⟨e, he⟩ : ∃ e : ℕ, ‖(l : PadicAlgCl l) ^ e * k‖ ≤ 1 := by
    have hl1 : ‖(l : PadicAlgCl l)‖ < 1 := norm_natCast_p_algCl_lt_one
    obtain ⟨e, he⟩ := exists_pow_lt_of_lt_one (show 0 < (‖k‖ + 1)⁻¹ by positivity) hl1
    refine ⟨e, ?_⟩
    rw [norm_mul, norm_pow]
    have h1 : 0 < ‖k‖ + 1 := by positivity
    calc ‖(l : PadicAlgCl l)‖ ^ e * ‖k‖ ≤ (‖k‖ + 1)⁻¹ * (‖k‖ + 1) :=
          mul_le_mul he.le (by linarith) (norm_nonneg _) (by positivity)
      _ = 1 := inv_mul_cancel₀ h1.ne'
  obtain ⟨w, hw⟩ := hK r (mul_mem (pow_mem (natCast_mem _ l) e) hk) he
  refine ⟨e, w, ?_⟩
  have hA : (l : Acris l) ^ e * a = tA l ^ n * r.w w :=
    iC_inj (pullback_fin_relation (fB l) (ACris.iotaB hE hZ) (DeRhamPotentiallySemistable.DRPst.iC l)
      ((algebraMap (BDeRhamPlus (normInteger ℂ_[l]) l) (BDeRham (normInteger ℂ_[l]) l)).comp (algClToBdR l : PadicAlgCl l →+* BDeRhamPlus (normInteger ℂ_[l]) l))
      iB_fB hT1 hky hw)
  exact fin2 B₀.c (B₀.t_unit.pow n) hna hA

end UpperTheory.Ru.crystallineComparison.PBI

/- English proof (translation)
Introduce `_ _ _ _ B₀ r` and use `UpperTheory.Ru.crystallineComparison.PBI.mainC B₀ r`.
-/
theorem UpperTheory.Ru.crystallineComparison.pbInv :
    ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (B₀ : PB l K) (r : Res l K), InvC B₀ r :=
  fun _ _ _ _ B₀ r => UpperTheory.Ru.crystallineComparison.PBI.mainC B₀ r
