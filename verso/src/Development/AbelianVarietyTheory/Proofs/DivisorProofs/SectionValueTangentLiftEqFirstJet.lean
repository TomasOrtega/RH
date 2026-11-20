import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
open Filter Topology

noncomputable section

namespace GlobalTheory.MBLow.EpsVal

open GlobalTheory.TangentOrigin

/- English proof (translation)
Establish `h' : ⊤ ≤ (x ≫ s) ⁻¹ᵁ V` using `fun p hp => e (h hp)`. Unfold `valR evalPt`. Rewrite using `[dif_pos h', ← Scheme.Hom.appLE_comp_appLE x s V U ⊤ e h]`. Both sides reduce to the same expression.
-/
theorem valR_comp_eq {R : Type} [CommRing R] {X Y : Scheme.{0}} (x : Sp R ⟶ X) (s : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (e : U ≤ s ⁻¹ᵁ V) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Y, V)) :
    valR (x ≫ s) V a = evalPt x U h ((s.appLE V U e).hom a) := by
  have h' : ⊤ ≤ (x ≫ s) ⁻¹ᵁ V := fun p hp => e (h hp)
  unfold valR evalPt
  rw [dif_pos h', ← Scheme.Hom.appLE_comp_appLE x s V U ⊤ e h]
  rfl

def sec (A : Over (Sp ℂ)) : A ⟶ baseOver (Sp ℂ) ⊗ A :=
  lift (Over.homMk A.hom (by simp) : A ⟶ baseOver (Sp ℂ)) (𝟙 A)

/- English proof (translation)
Rewrite using `[← Over.comp_left, sec, lift_snd, Over.id_left]`.
-/
theorem sec_snd (A : Over (Sp ℂ)) : (sec A).left ≫ (snd (baseOver (Sp ℂ)) A).left = 𝟙 A.left := by
  rw [← Over.comp_left, sec, lift_snd, Over.id_left]

/- English proof (translation)
Rewrite using `[← Over.comp_left, sec, comp_lift, Category.comp_id, epsLift]`. Use `congr 2`. Use `ext`. Simplify using the standard rewrite rules.
-/
theorem epsLift_eq {A : Over (Sp ℂ)} (v : epsR ℂ ⟶ A) : epsLift v = v.left ≫ (sec A).left := by
  rw [← Over.comp_left, sec, comp_lift, Category.comp_id, epsLift]
  congr 2
  ext
  simp

/- English proof (translation)
Rewrite using `[← Over.comp_left, sec, comp_lift, Category.comp_id, ptSecT]`. Use `congr 2`. Use `ext`. Simplify using `using (Over.w z).symm`.
-/
theorem ptSecT_eq {A : Over (Sp ℂ)} (z : baseOver (Sp ℂ) ⟶ A) :
    (ptSecT A z).left = z.left ≫ (sec A).left := by
  rw [← Over.comp_left, sec, comp_lift, Category.comp_id, ptSecT]
  congr 2
  ext
  simpa using (Over.w z).symm

/- English proof (translation)
Introduce `p hp`. Use `Set.mem_iInter.2 fun _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((sec A).left ≫ (snd (baseOver (Sp ℂ)) A).left) p ∈ L.U i`. Rewrite using `[sec_snd]`. Conclude with `hp`.
-/
theorem le_sec {A : Over (Sp ℂ)} (L : LB A.left) (k : ℤ) (i : L.ι) :
    L.U i ≤ (sec A).left ⁻¹ᵁ ((LPow A L k (baseOver (Sp ℂ))).U fun _ => i) := by
  intro p hp
  refine Set.mem_iInter.2 fun _ => ?_
  change ((sec A).left ≫ (snd (baseOver (Sp ℂ)) A).left) p ∈ L.U i
  rw [sec_snd]
  exact hp

/- English proof (translation)
Introduce `g P u k t f v W i hf hd hv hW hi`. Establish `h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ P.L.U i`. Rewrite using `[ex_zero_left]`. Conclude with `hi`. Establish `h : ⊤ ≤ v.left ⁻¹ᵁ P.L.U i` using `(tangent_mem_iff (u := u) hv _).2 h0`.

Use `set a := ((sec P.A).left.appLE _ _ (le_sec P.L (k : ℤ) i)).hom (t.f fun _ => i) with ha`. Establish `hval : ∀ z (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i), evalPt (R` using `ℂ) (u.ex z).left (P.L.U i) hz a = f z * u.fr i z ^ k := by`. Introduce `z hz`. Use `hf i z hz` as an intermediate fact. Rewrite `this` using `[ptSecT_eq]`.

Conclude with `(valR_comp_eq (R := ℂ) (u.ex z).left (sec P.A).left _ _ (le_sec P.L (k : ℤ) i) hz _).symm.trans this`. Establish `hev : (fun z => valAt' (u.ex z).left (P.L.U i) a) =ᶠ[𝓝 0] fun z => f z * u.fr i z ^ k` using `by filter_upwards [eventually_mem u h0] with z hz`. Rewrite using `[valAt'_eq_evalPt _ _ hz, hval z hz]`. Establish `hfr : DifferentiableAt ℂ (u.fr i) 0` using `(u.fr_hol i).differentiableAt (eventually_mem u h0)`. Establish `hne : u.fr i 0 ≠ 0` using `u.fr_ne i 0 h0`.

Establish `hD` using `((hd 0).hasFDerivAt.mul (hfr.hasFDerivAt.pow k)).fderiv`. Rewrite using `[epsLift_eq]`. Use `(valR_comp_eq (R := DualNumber ℂ) v.left (sec P.A).left _ _ (le_sec P.L (k : ℤ) i) h _).trans ?_` and prove the remaining obligations. Use `TrivSqZeroExt.ext ?_ ?_` and prove the remaining obligations. Use `(tangent_fst (u := u) hv h h0 a).trans ?_` and prove the remaining obligations.

Rewrite using `[hval 0 h0]`. Simplify using `[mul_comm]`. Use `(hW _ h a).trans ?_` and prove the remaining obligations. Rewrite using `[hev.fderiv_eq]`. Use `(congrArg (fun φ => φ W) hD).trans ?_` and prove the remaining obligations.

Break down `k with _ | k` into its components or cases. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem valR_epsLift : ∀ (g : ℕ) (P : PolAV (Sp ℂ)) (u : HolUnif P.A P.L g) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ)))) (f : (Fin g → ℂ) → ℂ) (v : epsR ℂ ⟶ P.A) (W : Fin g → ℂ) (i : P.L.ι), FnT u k t f → Differentiable ℂ f → IsTangent v → u.IsDiff W v → ⊤ ≤ (eSec P.A) ⁻¹ᵁ P.L.U i → valR (epsLift v) ((LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ))).U fun _ => i) (t.f fun _ => i) = TrivSqZeroExt.inl (u.fr i 0 ^ k) * (TrivSqZeroExt.inl (f 0) + TrivSqZeroExt.inr (fderiv ℂ f 0 W + (k * fderiv ℂ (u.fr i) 0 W / u.fr i 0) * f 0)) := by
  intro g P u k t f v W i hf hd hv hW hi
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ P.L.U i := by
    rw [ex_zero_left]; exact hi
  have h : ⊤ ≤ v.left ⁻¹ᵁ P.L.U i := (tangent_mem_iff (u := u) hv _).2 h0
  set a := ((sec P.A).left.appLE _ _ (le_sec P.L (k : ℤ) i)).hom (t.f fun _ => i) with ha
  have hval : ∀ z (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i),
      evalPt (R := ℂ) (u.ex z).left (P.L.U i) hz a = f z * u.fr i z ^ k := by
    intro z hz
    have := hf i z hz
    rw [ptSecT_eq] at this
    exact (valR_comp_eq (R := ℂ) (u.ex z).left (sec P.A).left _ _ (le_sec P.L (k : ℤ) i) hz _).symm.trans this
  have hev : (fun z => valAt' (u.ex z).left (P.L.U i) a) =ᶠ[𝓝 0] fun z => f z * u.fr i z ^ k := by
    filter_upwards [eventually_mem u h0] with z hz
    rw [valAt'_eq_evalPt _ _ hz, hval z hz]
  have hfr : DifferentiableAt ℂ (u.fr i) 0 := (u.fr_hol i).differentiableAt (eventually_mem u h0)
  have hne : u.fr i 0 ≠ 0 := u.fr_ne i 0 h0
  have hD := ((hd 0).hasFDerivAt.mul (hfr.hasFDerivAt.pow k)).fderiv
  rw [epsLift_eq]
  refine (valR_comp_eq (R := DualNumber ℂ) v.left (sec P.A).left _ _ (le_sec P.L (k : ℤ) i) h _).trans ?_
  refine TrivSqZeroExt.ext ?_ ?_
  · refine (tangent_fst (u := u) hv h h0 a).trans ?_
    rw [hval 0 h0]
    simp [mul_comm]
  · refine (hW _ h a).trans ?_
    rw [hev.fderiv_eq]
    refine (congrArg (fun φ => φ W) hD).trans ?_
    rcases k with _ | k
    · simp
    · simp
      field_simp
      ring

end GlobalTheory.MBLow.EpsVal

end
