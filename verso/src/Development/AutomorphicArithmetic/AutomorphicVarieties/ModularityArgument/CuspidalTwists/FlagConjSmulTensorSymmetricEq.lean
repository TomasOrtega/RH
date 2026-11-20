import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InertiaActsTriviallyOnRootsOfUnity
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix

namespace UpperTheory.V.Cu.SymplecticFlagConjugation

section Alg

variable {R : Type} [CommRing R]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [flg, tn, low, nA, Matrix.mul_apply, Fin.sum_univ_four]`.
-/
theorem flg_eq (x s : R) : flg x s = !![1, 0, 0, 0; s, 1, 0, 0; -(x * s), -x, 1, 0; x, 0, -s, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flg, tn, low, nA, Matrix.mul_apply, Fin.sum_univ_four]

/- English proof (translation)
Rewrite using `[flg_eq]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]`.
-/
theorem adj_flg (x s : R) : adj (flg x s) = !![1, 0, 0, 0; -s, 1, 0, 0; 0, x, 1, 0; -x, x * s, s, 1] := by
  rw [flg_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

/- English proof (translation)
Unfold `IsGSp`. Rewrite using `[adj_flg, flg_eq]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring`.
-/
theorem isGSp_flg (x s : R) : IsGSp 1 (flg x s) := by
  unfold IsGSp
  rw [adj_flg, flg_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/- English proof (translation)
Unfold `IsGSp`. Rewrite using `[Matrix.det_fin_two]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [tn, adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> first`. Consider the case `ring1`.

Consider the case `linear_combination (d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) * h00`. Consider the case `linear_combination (d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) * h01`. Consider the case `linear_combination (-(d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0))) * h01`. Consider the case `linear_combination (-(d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0))) * h11`.
-/
theorem gsp_tn (d : R) (g t : Matrix (Fin 2) (Fin 2) R) (h00 : t 0 0 * t 0 0 - t 1 0 * t 1 0 = 1)
    (h01 : t 0 0 * t 0 1 - t 1 0 * t 1 1 = 0) (h11 : t 0 1 * t 0 1 - t 1 1 * t 1 1 = -1) :
    IsGSp (d ^ 2 * g.det) (d • tn g t) := by
  unfold IsGSp
  rw [Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn, adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first
    | ring1
    | linear_combination (d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) * h00
    | linear_combination (d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0)) * h01
    | linear_combination (-(d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0))) * h01
    | linear_combination (-(d ^ 2 * (g 0 0 * g 1 1 - g 0 1 * g 1 0))) * h11

/- English proof (translation)
Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, adj_flg, flg_eq]`. Use `congr 1`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [tn, Matrix.mul_apply, Fin.sum_univ_four] <;> first`. Consider the case `ring1`.

Consider the case `linear_combination (-(b * (p + q * x))) * hs`. Consider the case `linear_combination (-(b * (q * x - r))) * hs`. Consider the case `linear_combination (b * (p + q * x)) * hs`. Consider the case `linear_combination (b * (q * x - r)) * hs`. Consider the case `linear_combination (q * a) * hs`.
-/
theorem flag_conj_smul_tensor_symmetric_eq (x s d a b p q r : R) (hs : s * s = 1) :
    adj (flg x s) * (d • tn !![p, q; (p + q * x) * x - r * x, r] !![a, b; b, a]) * flg x s =
      d • !![(a + b * s) * (p + q * x), b * (p + q * x), -(q * (a * s + b)), a * q;
        0, (a - b * s) * (p + q * x), 0, -(q * (a * s - b));
        0, 0, (a + b * s) * (r - x * q), -(b * (r - x * q));
        0, 0, 0, (a - b * s) * (r - x * q)] := by
  rw [Matrix.mul_smul, Matrix.smul_mul, adj_flg, flg_eq]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first
    | ring1
    | linear_combination (-(b * (p + q * x))) * hs
    | linear_combination (-(b * (q * x - r))) * hs
    | linear_combination (b * (p + q * x)) * hs
    | linear_combination (b * (q * x - r)) * hs
    | linear_combination (q * a) * hs

/- English proof (translation)
Establish `e1 : g = !![g 0 0, g 0 1; (g 0 0 + g 0 1 * x) * x - g 1 1 * x, g 1 1]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp <;> linear_combination hf`. Establish `e2 : t = !![t 0 0, t 0 1; t 0 1, t 0 0]`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [ht.1, ht.2]`. Use `conv_lhs => rw [e1, e2]`. Conclude with `flag_conj_smul_tensor_symmetric_eq x s d (t 0 0) (t 0 1) (g 0 0) (g 0 1) (g 1 1) hs`.
-/
theorem conj_flg (x s d : R) (g t : Matrix (Fin 2) (Fin 2) R) (hs : s * s = 1)
    (hf : g 1 0 + g 1 1 * x = (g 0 0 + g 0 1 * x) * x) (ht : t 1 1 = t 0 0 ∧ t 1 0 = t 0 1) :
    adj (flg x s) * (d • tn g t) * flg x s =
      d • !![(t 0 0 + t 0 1 * s) * (g 0 0 + g 0 1 * x), t 0 1 * (g 0 0 + g 0 1 * x), -(g 0 1 * (t 0 0 * s + t 0 1)), t 0 0 * g 0 1;
        0, (t 0 0 - t 0 1 * s) * (g 0 0 + g 0 1 * x), 0, -(g 0 1 * (t 0 0 * s - t 0 1));
        0, 0, (t 0 0 + t 0 1 * s) * (g 1 1 - x * g 0 1), -(t 0 1 * (g 1 1 - x * g 0 1));
        0, 0, 0, (t 0 0 - t 0 1 * s) * (g 1 1 - x * g 0 1)] := by
  have e1 : g = !![g 0 0, g 0 1; (g 0 0 + g 0 1 * x) * x - g 1 1 * x, g 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linear_combination hf
  have e2 : t = !![t 0 0, t 0 1; t 0 1, t 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ht.1, ht.2]
  conv_lhs => rw [e1, e2]
  exact flag_conj_smul_tensor_symmetric_eq x s d (t 0 0) (t 0 1) (g 0 0) (g 0 1) (g 1 1) hs

/- English proof (translation)
Establish `e00` using `congrFun (congrFun h 0) 0`. Establish `e01` using `congrFun (congrFun h 0) 1`. Establish `e11` using `congrFun (congrFun h 1) 1`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e11`. Conclude with `⟨by linear_combination e00, by linear_combination e01, by linear_combination e11⟩`.
-/
theorem form_eqs (t : Matrix (Fin 2) (Fin 2) R) (h : tᵀ * !![1, 0; 0, -1] * t = !![1, 0; 0, -1]) :
    t 0 0 * t 0 0 - t 1 0 * t 1 0 = 1 ∧ t 0 0 * t 0 1 - t 1 0 * t 1 1 = 0 ∧ t 0 1 * t 0 1 - t 1 1 * t 1 1 = -1 := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e11
  exact ⟨by linear_combination e00, by linear_combination e01, by linear_combination e11⟩

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[adj_apply]`.
-/
theorem symplecticAdjoint_map_ringHom {R' : Type} [CommRing R'] (f : R →+* R') (X : M4 R) : adj (X.map f) = (adj X).map f := by
  ext i j
  simp [adj_apply]

/- English proof (translation)
Rewrite using `[symplecticAdjoint_map_ringHom, ← Matrix.map_mul, ← Matrix.map_mul]`.
-/
theorem conj_map {R' : Type} [CommRing R'] (f : R →+* R') (N M : M4 R) :
    adj (N.map f) * M.map f * N.map f = (adj N * M * N).map f := by
  rw [symplecticAdjoint_map_ringHom, ← Matrix.map_mul, ← Matrix.map_mul]

/- English proof (translation)
Unfold `IsGSp at *`. Rewrite using `[symplecticAdjoint_map_ringHom, ← Matrix.map_mul, h]`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [hij]`.
-/
theorem gsp_map {R' : Type} [CommRing R'] (f : R →+* R') {ν : R} {M : M4 R} (h : IsGSp ν M) : IsGSp (f ν) (M.map f) := by
  unfold IsGSp at *
  rw [symplecticAdjoint_map_ringHom, ← Matrix.map_mul, h]
  ext i j
  by_cases hij : i = j <;> simp [hij]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h.1, h.2, ih.1, ih.2]`.
-/
theorem pow_diag {g : M2 R} (h : g 0 1 = 0 ∧ g 1 0 = 0) (n : ℕ) :
    (g ^ n) 0 1 = 0 ∧ (g ^ n) 1 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h.1, h.2, ih.1, ih.2]

/- English proof (translation)
Establish `e` using `congrArg (residue O) (Units.inv_mul u)`. Rewrite `e` using `[map_mul, h, mul_one, map_one]`. Then use the resulting hypothesis.
-/
theorem res_inv {O : Type} [CommRing O] [IsLocalRing O] (u : Oˣ) (h : residue O (u : O) = 1) :
    residue O ((u⁻¹ : Oˣ) : O) = 1 := by
  have e := congrArg (residue O) (Units.inv_mul u)
  rwa [map_mul, h, mul_one, map_one] at e

end Alg

end UpperTheory.V.Cu.SymplecticFlagConjugation

open UpperTheory.V.Cu.SymplecticFlagConjugation in
/- English proof (translation)
Introduce `Ω _ _ _ l _ d T hT hok W R _ f hdet hθ`. Establish `hr : ∀ g, ((d.Q T).map f).r g = ((inc d.h (d.δ (resQ T.F g) : d.c.O)) • tn (d.ρ₁ (resQ T.F g)) (d.τ (resQ T.F g))).map f` using `fun g => rfl`. Establish `hn : ∀ v, ((d.Q T).map f).n v = (flg (d.x (T.pl v)) (d.s (T.pl v))).map f` using `fun v => rfl`. Establish `hF : ∀ g : G T.F Ω, resQ T.F g ∈ T.F.fixingSubgroup` using `fun g x => g.commutes x`. Establish `hcyc : ∀ g : G T.F Ω, cycZ ℚ Ω l (resQ T.F g) = cycZ T.F Ω l g` using `fun g => rfl`.

Establish `hD : ∀ A, ∀ g ∈ Dec (F` using `T.F) A, resQ T.F g ∈ Dec (F := ℚ) A := fun A g h => mem_Dec.2 (mem_Dec.1 h)`. Establish `hI : ∀ A, ∀ g ∈ Ine (F` using `T.F) A, resQ T.F g ∈ Ine (F := ℚ) A := fun A g h => mem_Ine.2 (mem_Ine.1 h)`. Establish `hsgn : ∀ A, d.s A * d.s A = 1` using `fun A => by`. Apply the tactic sequence `rcases d.tau.sgn A with h | h <;> rw [h] <;> ring`. Use `⟨fun g => ?_, ?_, ?_, fun v => ?_, fun v s hs => ?_, fun v s hs i => ?_⟩` and prove the remaining obligations.

Take `⟨h00, h01, h11⟩` from `form_eqs _ (d.tau.form (resQ T.F g))`. Establish `h1` using `gsp_map f (gsp_tn (inc d.h (d.δ (resQ T.F g) : d.c.O)) (d.ρ₁ (resQ T.F g)) _ h00 h01 h11)`. Establish `key : inc d.h (d.δ (resQ T.F g) : d.c.O) ^ 2 * inc d.h (Phi d.D d.T₀.pr d.k (resQ T.F g) : d.c.O) = inc d.h (d.D.th (resQ T.F g) : d.c.O)`. Rewrite using `[← map_pow, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, d.tw.mul]`. Rewrite `h1` using `[map_mul, hdet _ (hF g), ← map_mul, key]`.

Conclude with `h1`. Introduce and unpack `g ⟨A, hA, hg, h1⟩`. Establish `hl` using `hA l (Finset.mem_insert_self _ _)`. Establish `hI'` using `hI A g hg`. Establish `h2` using `d.tw.kill _ ((places ℚ Ω l A).2.2.2 hl hI') h1`.

Establish `hK : resQ T.F g ∈ d.K'.fixingSubgroup`. Assume the negation of the conclusion as `hn'`. Establish `hres : resQ d.T₀.F (resLe hT.le g) = resQ T.F g` using `AlgEquiv.ext fun _ => rfl`. Establish `hoff` using `d.quad.off (resLe hT.le g) (by rwa [hres])`. Establish `hb : ∀ j, residue d.c.O (d.D.ps j (resQ T.F g) : d.c.O) = 1` using `fun j => by`.

Establish `e` using `congrFun (congrFun h1 j) j`. Simplify `e` using `[Raw.rbar, Raw.r0, diagRep]`. Establish `hon : d.T₀.rb wAl (resLe hT.le g) = 1` using `by show residue d.c.O (((chi d.D d.T₀.pr 0 (resQ T.F g) * (chi d.D d.T₀.pr 1 (resQ T.F g))⁻¹) ^ (1 : ℤ) * (chi d.D d.T₀.pr 0 (resQ T.F g) * (chi d.D d.T₀.pr 2 (resQ T.F g))⁻¹) ^ (0 : ℤ) : d.c.Oˣ) : d.c.O) = 1`. Establish `hb' : ∀ i, residue d.c.O (chi d.D d.T₀.pr i (resQ T.F g) : d.c.O) = 1` using `fun i => hb (lab d.T₀.pr i)`. Rewrite using `[zpow_one, zpow_zero, mul_one, Units.val_mul, map_mul, hb', res_inv _ (hb' 1), mul_one]`.

Use `(UpperTheory.V.Ws.P1.coefRes d.c).2.1` as an intermediate fact. Conclude with `Ring.neg_one_ne_one_of_char_ne_two (by rw [ringChar.eq (ResidueField d.c.O) l]; exact d.ctx.1.l_odd) (hoff.symm.trans hon)`. Establish `h3` using `d.tau.unr A hl _ hI' hK`. Establish `h4` using `d.mod.away A hl _ hI' h2.2 (hθ A hA g hg)`. Use `(hr g).trans ?_` and prove the remaining obligations.

Rewrite using `[h2.1, h3, h4, tn_one]`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`. Take `⟨j, hj⟩` from `hT.g0`. Establish `hρ` using `pow_diag d.mod.nrm (l ^ j)`.

Establish `hτ` using `pow_diag (g := d.τ (resQ d.T₀.F d.T₀.g0)) (by rw [d.tau.nrm]; simp) (l ^ j)`. Rewrite `hρ`, `hτ` using `[← map_pow, ← hj]`. Introduce `a b hab`. Use `(congrFun (congrFun (hr T.g0) a) b).trans ?_` and prove the remaining obligations. Generalize the expression as in `resQ T.F T.g0 = g1 at hρ hτ ⊢`.

Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [tn, hρ.1, hρ.2, hτ.1, hτ.2] at hab ⊢`. Express the relevant statement in the definitionally equal form `IsLow ((flg (d.x (T.pl v)) (d.s (T.pl v))).map f)`. Use `⟨?_, fun i => ?_, fun i j hij => ?_⟩` and prove the remaining obligations. Simplify using `using gsp_map f (isGSp_flg (d.x (T.pl v)) (d.s (T.pl v)))`. Apply the tactic sequence `rw [flg_eq] fin_cases i <;> simp`.

Apply the tactic sequence `rw [flg_eq] fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp`. Establish `hsD` using `hD _ s hs`. Express the relevant statement in the definitionally equal form `IsUp (adj ((flg (d.x (T.pl v)) (d.s (T.pl v))).map f) * ((inc d.h (d.δ (resQ T.F s) : d.c.O)) • tn (d.ρ₁ (resQ T.F s)) (d.τ (resQ T.F s))).map f * (flg (d.x (T.pl v)) (d.s (T.pl v))).map f)`. Rewrite using `[conj_map, conj_flg _ _ _ _ _ (hsgn _) (d.mod.flag _ (T.ovl v) _ hsD) (d.tau.on _ (d.quad.split _ (T.ovl v) hsD))]`. Introduce `i j hij`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp`. Take `⟨hi, hc⟩` from `UpperTheory.inertia_acts_trivially_on_roots_of_unity T.F Ω l d.ctx.1.l_odd _ (T.ovl v) s hs`. Establish `hc'` using `(hcyc s).trans hc`. Establish `hsD : resQ T.F s ∈ Dec (F` using `ℚ) (T.pl v) := hD _ s hs.1`. Establish `hsI` using `hI _ s hi`.

Establish `hK` using `d.quad.split _ (T.ovl v) hsD`. Establish `hδ` using `(d.tw.kill _ hc' (hok.ineL _ (T.ovl v) s hi)).1`. Establish `hm` using `d.mod.ine _ (T.ovl v) _ hsI`. Establish `h3 : chiO ℚ Ω l d.c₁.O (resQ T.F s) = 1` using `by show Units.map _ (cycZ ℚ Ω l _) = 1`. Rewrite using `[hc', map_one]`.

Establish `ht` using `d.tau.ine _ (T.ovl v) _ hsI`. Rewrite `ht`, `hm` using `[h3, one_pow, Units.val_one]`. Take `⟨h00, -, -⟩` from `form_eqs _ (d.tau.form (resQ T.F s))`. Establish `hon` using `d.tau.on _ hK`. Establish `hss` using `hsgn (T.pl v)`.

Establish `h4 : d.τ (resQ T.F s) 0 0 - d.τ (resQ T.F s) 0 1 * d.s (T.pl v) = 1`. Take the linear combination `(-(d.τ (resQ T.F s) 0 0 - d.τ (resQ T.F s) 0 1 * d.s (T.pl v))) * ht + h00 + (d.τ (resQ T.F s) 1 0 + d.τ (resQ T.F s) 0 1) * hon.2 + (-(d.τ (resQ T.F s) 0 1 ^ 2)) * hss`. Express the relevant statement in the definitionally equal form `(adj ((flg (d.x (T.pl v)) (d.s (T.pl v))).map f) * ((inc d.h (d.δ (resQ T.F s) : d.c.O)) • tn (d.ρ₁ (resQ T.F s)) (d.τ (resQ T.F s))).map f * (flg (d.x (T.pl v)) (d.s (T.pl v))).map f) i i = 1`. Rewrite using `[conj_map, conj_flg _ _ _ _ _ hss (d.mod.flag _ (T.ovl v) _ hsD) hon, hm.1, hm.2, ht, h4, hδ]`. Apply the tactic sequence `fin_cases i <;> simp`.
-/
theorem UpperTheory.V.Cu.pairOf4 : UpperTheory.V.Cu.PairOf4 := by
  intro Ω _ _ _ l _ d T hT hok W R _ f hdet hθ
  have hr : ∀ g, ((d.Q T).map f).r g =
      ((inc d.h (d.δ (resQ T.F g) : d.c.O)) • tn (d.ρ₁ (resQ T.F g)) (d.τ (resQ T.F g))).map f := fun g => rfl
  have hn : ∀ v, ((d.Q T).map f).n v = (flg (d.x (T.pl v)) (d.s (T.pl v))).map f := fun v => rfl
  have hF : ∀ g : G T.F Ω, resQ T.F g ∈ T.F.fixingSubgroup := fun g x => g.commutes x
  have hcyc : ∀ g : G T.F Ω, cycZ ℚ Ω l (resQ T.F g) = cycZ T.F Ω l g := fun g => rfl
  have hD : ∀ A, ∀ g ∈ Dec (F := T.F) A, resQ T.F g ∈ Dec (F := ℚ) A := fun A g h => mem_Dec.2 (mem_Dec.1 h)
  have hI : ∀ A, ∀ g ∈ Ine (F := T.F) A, resQ T.F g ∈ Ine (F := ℚ) A := fun A g h => mem_Ine.2 (mem_Ine.1 h)
  have hsgn : ∀ A, d.s A * d.s A = 1 := fun A => by
    rcases d.tau.sgn A with h | h <;> rw [h] <;> ring
  refine ⟨fun g => ?_, ?_, ?_, fun v => ?_, fun v s hs => ?_, fun v s hs i => ?_⟩
  · obtain ⟨h00, h01, h11⟩ := form_eqs _ (d.tau.form (resQ T.F g))
    have h1 := gsp_map f (gsp_tn (inc d.h (d.δ (resQ T.F g) : d.c.O)) (d.ρ₁ (resQ T.F g)) _ h00 h01 h11)
    have key : inc d.h (d.δ (resQ T.F g) : d.c.O) ^ 2 * inc d.h (Phi d.D d.T₀.pr d.k (resQ T.F g) : d.c.O) =
        inc d.h (d.D.th (resQ T.F g) : d.c.O) := by
      rw [← map_pow, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, d.tw.mul]
    rw [map_mul, hdet _ (hF g), ← map_mul, key] at h1
    exact h1
  · rintro g ⟨A, hA, hg, h1⟩
    have hl := hA l (Finset.mem_insert_self _ _)
    have hI' := hI A g hg
    have h2 := d.tw.kill _ ((places ℚ Ω l A).2.2.2 hl hI') h1
    have hK : resQ T.F g ∈ d.K'.fixingSubgroup := by
      by_contra hn'
      have hres : resQ d.T₀.F (resLe hT.le g) = resQ T.F g := AlgEquiv.ext fun _ => rfl
      have hoff := d.quad.off (resLe hT.le g) (by rwa [hres])
      have hb : ∀ j, residue d.c.O (d.D.ps j (resQ T.F g) : d.c.O) = 1 := fun j => by
        have e := congrFun (congrFun h1 j) j
        simpa [Raw.rbar, Raw.r0, diagRep] using e
      have hon : d.T₀.rb wAl (resLe hT.le g) = 1 := by
        show residue d.c.O (((chi d.D d.T₀.pr 0 (resQ T.F g) * (chi d.D d.T₀.pr 1 (resQ T.F g))⁻¹) ^ (1 : ℤ) *
          (chi d.D d.T₀.pr 0 (resQ T.F g) * (chi d.D d.T₀.pr 2 (resQ T.F g))⁻¹) ^ (0 : ℤ) : d.c.Oˣ) : d.c.O) = 1
        have hb' : ∀ i, residue d.c.O (chi d.D d.T₀.pr i (resQ T.F g) : d.c.O) = 1 := fun i => hb (lab d.T₀.pr i)
        rw [zpow_one, zpow_zero, mul_one, Units.val_mul, map_mul, hb', res_inv _ (hb' 1), mul_one]
      have := (UpperTheory.V.Ws.P1.coefRes d.c).2.1
      exact Ring.neg_one_ne_one_of_char_ne_two (by rw [ringChar.eq (ResidueField d.c.O) l]; exact d.ctx.1.l_odd)
        (hoff.symm.trans hon)
    have h3 := d.tau.unr A hl _ hI' hK
    have h4 := d.mod.away A hl _ hI' h2.2 (hθ A hA g hg)
    refine (hr g).trans ?_
    rw [h2.1, h3, h4, tn_one]
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · obtain ⟨j, hj⟩ := hT.g0
    have hρ := pow_diag d.mod.nrm (l ^ j)
    have hτ := pow_diag (g := d.τ (resQ d.T₀.F d.T₀.g0)) (by rw [d.tau.nrm]; simp) (l ^ j)
    rw [← map_pow, ← hj] at hρ hτ
    intro a b hab
    refine (congrFun (congrFun (hr T.g0) a) b).trans ?_
    generalize resQ T.F T.g0 = g1 at hρ hτ ⊢
    fin_cases a <;> fin_cases b <;> simp [tn, hρ.1, hρ.2, hτ.1, hτ.2] at hab ⊢
  · change IsLow ((flg (d.x (T.pl v)) (d.s (T.pl v))).map f)
    refine ⟨?_, fun i => ?_, fun i j hij => ?_⟩
    · simpa using gsp_map f (isGSp_flg (d.x (T.pl v)) (d.s (T.pl v)))
    · rw [flg_eq]
      fin_cases i <;> simp
    · rw [flg_eq]
      fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp
  · have hsD := hD _ s hs
    change IsUp (adj ((flg (d.x (T.pl v)) (d.s (T.pl v))).map f) * ((inc d.h (d.δ (resQ T.F s) : d.c.O)) • tn (d.ρ₁ (resQ T.F s)) (d.τ (resQ T.F s))).map f * (flg (d.x (T.pl v)) (d.s (T.pl v))).map f)
    rw [conj_map, conj_flg _ _ _ _ _ (hsgn _) (d.mod.flag _ (T.ovl v) _ hsD)
      (d.tau.on _ (d.quad.split _ (T.ovl v) hsD))]
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp
  · obtain ⟨hi, hc⟩ := UpperTheory.inertia_acts_trivially_on_roots_of_unity T.F Ω l d.ctx.1.l_odd _ (T.ovl v) s hs
    have hc' := (hcyc s).trans hc
    have hsD : resQ T.F s ∈ Dec (F := ℚ) (T.pl v) := hD _ s hs.1
    have hsI := hI _ s hi
    have hK := d.quad.split _ (T.ovl v) hsD
    have hδ := (d.tw.kill _ hc' (hok.ineL _ (T.ovl v) s hi)).1
    have hm := d.mod.ine _ (T.ovl v) _ hsI
    have h3 : chiO ℚ Ω l d.c₁.O (resQ T.F s) = 1 := by
      show Units.map _ (cycZ ℚ Ω l _) = 1
      rw [hc', map_one]
    have ht := d.tau.ine _ (T.ovl v) _ hsI
    rw [h3, one_pow, Units.val_one] at ht hm
    obtain ⟨h00, -, -⟩ := form_eqs _ (d.tau.form (resQ T.F s))
    have hon := d.tau.on _ hK
    have hss := hsgn (T.pl v)
    have h4 : d.τ (resQ T.F s) 0 0 - d.τ (resQ T.F s) 0 1 * d.s (T.pl v) = 1 := by
      linear_combination (-(d.τ (resQ T.F s) 0 0 - d.τ (resQ T.F s) 0 1 * d.s (T.pl v))) * ht + h00 +
        (d.τ (resQ T.F s) 1 0 + d.τ (resQ T.F s) 0 1) * hon.2 + (-(d.τ (resQ T.F s) 0 1 ^ 2)) * hss
    change (adj ((flg (d.x (T.pl v)) (d.s (T.pl v))).map f) * ((inc d.h (d.δ (resQ T.F s) : d.c.O)) • tn (d.ρ₁ (resQ T.F s)) (d.τ (resQ T.F s))).map f * (flg (d.x (T.pl v)) (d.s (T.pl v))).map f) i i = 1
    rw [conj_map, conj_flg _ _ _ _ _ hss (d.mod.flag _ (T.ovl v) _ hsD) hon, hm.1, hm.2, ht, h4, hδ]
    fin_cases i <;> simp

end
