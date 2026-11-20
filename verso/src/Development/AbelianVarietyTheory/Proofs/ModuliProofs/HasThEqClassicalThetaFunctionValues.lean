import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsConstMulOfIsFnPowNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTwistPullMulFn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricLiftTorsionPointActionOnThetaStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenIsValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaClassical

/- English proof (translation)
Unfold `constFn`. Rewrite using `[map_mul, map_mul]`.
-/
theorem constFn_mul {X : Scheme.{0}} (f : X ⟶ Sp ℂ) (U : X.Opens) (a b : ℂ) :
    constFn f U (a * b) = constFn f U a * constFn f U b := by
  unfold constFn
  rw [map_mul, map_mul]

/- English proof (translation)
Unfold `constFn`. Rewrite using `[map_one, map_one]`.
-/
theorem constFn_one {X : Scheme.{0}} (f : X ⟶ Sp ℂ) (U : X.Opens) : constFn f U 1 = 1 := by
  unfold constFn
  rw [map_one, map_one]

/- English proof (translation)
Rewrite using `[Category.comp_id]`. Conclude with `congrArg (fun f : Γ(Sp ℂ, ⊤) ⟶ Γ((⊤ : (Sp ℂ).Opens).toScheme, (⊤ : (Sp ℂ).Opens).ι ⁻¹ᵁ ⊤) => f.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) (Scheme.Hom.appLE_eq_app (⊤ : (Sp ℂ).Opens).ι (U := ⊤)).symm`.
-/
theorem constFn_top (a : ℂ) :
    (⊤ : (Sp ℂ).Opens).ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) =
      constFn ((⊤ : (Sp ℂ).Opens).ι ≫ 𝟙 _) ⊤ a := by
  rw [Category.comp_id]
  exact congrArg (fun f : Γ(Sp ℂ, ⊤) ⟶ Γ((⊤ : (Sp ℂ).Opens).toScheme, (⊤ : (Sp ℂ).Opens).ι ⁻¹ᵁ ⊤) =>
    f.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
    (Scheme.Hom.appLE_eq_app (⊤ : (Sp ℂ).Opens).ι (U := ⊤)).symm

/- English proof (translation)
Establish `hC` using `GlobalTheory.Moduli.cube_of_isLB`. Take `⟨th, hgen, hth⟩` from `GlobalTheory.exists_isGenSec_of_isThetaFn hL hL2 hC hT P u Hm χ θ T p hAH hθ h0`. Take `⟨s1, α, c, hc, hα, htw, hs1⟩` from `GlobalTheory.exists_twistPull_mul_fn hL hL2 hC hT P u Hm χ N θ T p th hAH hN hth`. Take `⟨τ, hτ, hval⟩` from `GlobalTheory.OriginValue.exists_gen_isValueAt_origin P u ((N : ℤ) ^ 2) T p`. Use `choose U hU using hU`.

Use `choose s2 hs2 using fun i => GlobalTheory.ThetaPtExist.exists_isTwistPull P.isLB (Out.translT P.A (U i).pt) (Out.translPt P.A (U i).pt) (lift_snd _ _) ((N : ℤ) ^ 2) ((N : ℤ) ^ 2) (U i).φ (U i).isGen s1`. Establish `hact` using `fun i => GlobalTheory.T.symmetricLift_torsionPoint_action_on_theta hL hL2 hC hT P u Hm χ N (l i) (fun z => c * θ ((N : ℂ) • z)) T p (x i) (U i) s1 (s2 i) hAH hN (hx i) (hU i) (hs2 i) hs1`. Establish `hv` using `fun i => hval (s2 i) (fun z => χ (l i) * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) * hermForm Hm (l i) (l i) - Real.pi * hermForm Hm z (l i)) * (c * θ ((N : ℂ) • (z + ((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ))))) (hact i)`. Establish `hcu : IsUnit (constFn T.hom ⊤ c⁻¹)` using `IsUnit.of_mul_eq_one (constFn T.hom ⊤ c) (by rw [← constFn_mul, inv_mul_cancel₀ hc, constFn_one])`. Establish `hN0 : (N : ℂ) ≠ 0` using `by exact_mod_cast hN.pos.ne'`.

Use `⟨th, s1, α, τ, U, s2, _, hcu.unit, hgen, hα, hτ, htw, hU, hs2, hv, fun i => ?_⟩` and prove the remaining obligations. Use `Eq.trans (congrArg (constFn T.hom ⊤) ?_) (constFn_mul T.hom ⊤ c⁻¹ _)` and prove the remaining obligations. Establish `e1 : hermForm Hm 0 (l i) = 0` using `by simp [hermForm]`. Establish `e2 : (N : ℂ) • (0 + ((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ)) = (N : ℂ)⁻¹ • (l i : Fin P.g → ℂ)`. Rewrite using `[zero_add, smul_smul]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Simplify using `only [e1, e2, mul_zero, sub_zero]`. Clear the denominators using the available nonvanishing facts.
-/
theorem isThetaPtOver (hL : Out.Laws) (hL2 : Out.Laws2) (hT : ThetaUnifAV) (P : Out.PolAV (Sp ℂ))
    (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ)
    (θ : (Fin P.g → ℂ) → ℂ) (N : ℕ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
    {I : Type} (x : I → (T ⟶ P.A)) (l : I → u.Λ) (hN : Odd N) (hAH : u.IsAH Hm χ)
    (hθ : u.IsThetaFn Hm χ 1 θ) (h0 : θ ≠ 0)
    (hx : ∀ i, p ≫ x i = u.ex (((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ)))
    (hU : ∀ i, ∃ U : Out.ThetaGrp P.A P.L ((N : ℤ) ^ 2) T,
      Out.SymLift P.A P.L ((N : ℤ) ^ 2) (N ^ 2) (x i) U) :
    Out.IsThetaPtOver P N x (fun i => constFn T.hom ⊤
      (χ (l i) * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) * hermForm Hm (l i) (l i)) *
        θ ((N : ℂ)⁻¹ • (l i : Fin P.g → ℂ)))) := by
  have hC := GlobalTheory.Moduli.cube_of_isLB
  obtain ⟨th, hgen, hth⟩ := GlobalTheory.exists_isGenSec_of_isThetaFn hL hL2 hC hT P u Hm χ θ T p hAH hθ h0
  obtain ⟨s1, α, c, hc, hα, htw, hs1⟩ := GlobalTheory.exists_twistPull_mul_fn hL hL2 hC hT P u Hm χ N θ T p th hAH hN hth
  obtain ⟨τ, hτ, hval⟩ := GlobalTheory.OriginValue.exists_gen_isValueAt_origin P u ((N : ℤ) ^ 2) T p
  choose U hU using hU
  choose s2 hs2 using fun i => GlobalTheory.ThetaPtExist.exists_isTwistPull P.isLB (Out.translT P.A (U i).pt)
    (Out.translPt P.A (U i).pt) (lift_snd _ _) ((N : ℤ) ^ 2) ((N : ℤ) ^ 2) (U i).φ (U i).isGen s1
  have hact := fun i => GlobalTheory.T.symmetricLift_torsionPoint_action_on_theta hL hL2 hC hT P u Hm χ N (l i) (fun z => c * θ ((N : ℂ) • z)) T p
    (x i) (U i) s1 (s2 i) hAH hN (hx i) (hU i) (hs2 i) hs1
  have hv := fun i => hval (s2 i) (fun z => χ (l i) * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) *
    hermForm Hm (l i) (l i) - Real.pi * hermForm Hm z (l i)) *
      (c * θ ((N : ℂ) • (z + ((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ))))) (hact i)
  have hcu : IsUnit (constFn T.hom ⊤ c⁻¹) :=
    IsUnit.of_mul_eq_one (constFn T.hom ⊤ c) (by rw [← constFn_mul, inv_mul_cancel₀ hc, constFn_one])
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.pos.ne'
  refine ⟨th, s1, α, τ, U, s2, _, hcu.unit, hgen, hα, hτ, htw, hU, hs2, hv, fun i => ?_⟩
  refine Eq.trans (congrArg (constFn T.hom ⊤) ?_) (constFn_mul T.hom ⊤ c⁻¹ _)
  have e1 : hermForm Hm 0 (l i) = 0 := by simp [hermForm]
  have e2 : (N : ℂ) • (0 + ((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ)) = (N : ℂ)⁻¹ • (l i : Fin P.g → ℂ) := by
    rw [zero_add, smul_smul]
    congr 1
    field_simp
  simp only [e1, e2, mul_zero, sub_zero]
  field_simp

/- English proof (translation)
Substitute `hk` using the available equality. Establish `hu : IsUnit (n : Γ(Sp ℂ, ⊤))`. Establish `h : IsUnit (n : ℂ)` using `IsUnit.mk0 _ (by exact_mod_cast hn.pos.ne')`. Simplify using `using h.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom`. Take `⟨V, hV, U, hU⟩` from `(hL.symLift (Sp ℂ) P n hn hu _ x hx).1 (default : PrimeSpectrum ℂ)`.

Choose the witnesses or unpack the hypotheses as in `rfl : V = ⊤ := by`. Use `top_le_iff.1 fun y _ => ?_` and prove the remaining obligations. Establish `: y = (default : PrimeSpectrum ℂ)` using `Subsingleton.elim (α := PrimeSpectrum ℂ) _ _`. Rewrite using `[this]`. Conclude with `hV`.

Conclude with `⟨U, hU⟩`.
-/
theorem exists_symLift (hL : Out.Laws) (P : Out.PolAV (Sp ℂ)) (n : ℕ) (k : ℤ) (hk : k = n) (hn : Odd n)
    (x : Out.baseOver (Sp ℂ) ⟶ P.A) (hx : x ^ n = 1) :
    ∃ U : Out.ThetaGrp P.A P.L k (Out.overRes (T := Out.baseOver (Sp ℂ)) ⊤),
      Out.SymLift P.A P.L k n (Out.overResι ⊤ ≫ x) U := by
  subst hk
  have hu : IsUnit (n : Γ(Sp ℂ, ⊤)) := by
    have h : IsUnit (n : ℂ) := IsUnit.mk0 _ (by exact_mod_cast hn.pos.ne')
    simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  obtain ⟨V, hV, U, hU⟩ := (hL.symLift (Sp ℂ) P n hn hu _ x hx).1 (default : PrimeSpectrum ℂ)
  obtain rfl : V = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    have : y = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [this]
    exact hV
  exact ⟨U, hU⟩

/- English proof (translation)
The claim follows from `(u.ker 0).2 u.Λ.zero_mem`.
-/
theorem ex_zero {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) :
    u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_smul, pow_zero, ex_zero]`. Consider the case `succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]`.
-/
theorem ex_nsmul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (z : Fin g → ℂ) (n : ℕ) : u.ex (n • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, ex_zero]
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => simp [Out.linComb, ex_zero]`. Consider the case `succ r ih`. Rewrite using `[Fin.sum_univ_succ, u.ex_add, ih, ex_nsmul]`. Simplify using `[Out.linComb, List.ofFn_succ]`.
-/
theorem ex_sum {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    {r : ℕ} (z : Fin r → Fin g → ℂ) (a : Fin r → ℕ) :
    u.ex (∑ i, a i • z i) = Out.linComb (fun i => u.ex (z i)) a := by
  induction r with
  | zero => simp [Out.linComb, ex_zero]
  | succ r ih =>
    rw [Fin.sum_univ_succ, u.ex_add, ih, ex_nsmul]
    simp [Out.linComb, List.ofFn_succ]

/- English proof (translation)
Introduce `hL hL2 hT o _ g N' J b em t u Hm χ θ lam hN hAH hθ h0 hpt`. Establish `hN0 : (N' : ℂ) ≠ 0` using `by exact_mod_cast hN.pos.ne'`. Use `haveI := t.ab.comm`. Use `⟨hN, ?_, fun q => ⟨⊤, trivial, ?_⟩⟩` and prove the remaining obligations. Establish `h : IsUnit (N' : ℂ)` using `IsUnit.mk0 _ hN0`.

Establish `h'` using `h.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom`. Rewrite `h'` using `[map_natCast]`. Conclude with `h'`. Set `T : Over (Sp ℂ)` to `Out.overRes (T := Out.baseOver (Sp ℂ)) ⊤`. Use `haveI : IsIso T.hom := by show IsIso ((⊤ : (Sp ℂ).Opens).ι ≫ 𝟙 _)`.

Rewrite using `[Category.comp_id]`. Conclude with `inferInstanceAs (IsIso (Sp ℂ).topIso.hom)`. Set `p : 𝟙_ (Over (Sp ℂ)) ⟶ T` to `Over.homMk (inv T.hom) (by simp)`. Establish `hp : p ≫ Out.overResι (T` using `Out.baseOver (Sp ℂ)) ⊤ = 𝟙 _ := by ext1 show inv T.hom ≫ (⊤ : (Sp ℂ).Opens).ι = 𝟙 _`. Rewrite using `[IsIso.inv_comp_eq]`.

Both sides reduce to the same expression. Establish `hpt' : t.pt = fun i => u.ex (((N' : ℂ) ^ 2)⁻¹ • (lam i : Fin g → ℂ))`. Use function extensionality and compare the values at `fun i => Over.OverMorphism.ext (hpt i)`. Establish `hcoe : ∀ a : Ix g (N' ^ 2), ((∑ i, ((a i).val : ℤ) • lam i : u.Λ) : Fin g → ℂ) = ∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ)` using `fun a => by`. Rewrite using `[Submodule.coe_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, natCast_zsmul, Nat.cast_smul_eq_nsmul]`. Establish `hlab : ∀ a : Ix g (N' ^ 2), t.lab a = u.ex (((N' : ℂ) ^ 2)⁻¹ • ((∑ i, ((a i).val : ℤ) • lam i : u.Λ) : Fin g → ℂ))` using `fun a => by`. Rewrite using `[hcoe, Finset.smul_sum, TObj.lab, hpt']`. Use `(ex_sum u _ _).symm.trans (congrArg u.ex (Finset.sum_congr rfl fun i _ => ?_))` and prove the remaining obligations.

Rewrite using `[smul_comm, Nat.cast_smul_eq_nsmul]`. Establish `htor : ∀ a : Ix g (N' ^ 2), t.lab a ^ (N' ^ 2) = 1` using `fun a => by`. Rewrite using `[TObj.lab, Out.linComb, List.prod_ofFn, ← Finset.prod_pow]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm, pow_mul, t.torsion, one_pow]`.

Establish `key` using `isThetaPtOver hL hL2 hT t.pol u Hm χ θ N' T p (fun a : Ix g (N' ^ 2) => Out.overResι ⊤ ≫ t.lab a) (fun a => ∑ i, ((a i).val : ℤ) • lam i) hN hAH hθ h0 (fun a => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ t.lab a) hp).trans ((Category.id_comp _).trans (hlab a)))) (fun a => …`. Use `key using 2 with a a` and compare the differences between its conclusion and the goal. Use `congr 1`. Use `(constFn_top _).trans ?_` and prove the remaining obligations. Use `congrArg (constFn T.hom ⊤) ?_` and prove the remaining obligations.

Conclude with `congrArg (fun w : Fin g → ℂ => χ (∑ i, ((a i).val : ℤ) • lam i) * Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * hermForm Hm w w) * θ ((N' : ℂ)⁻¹ • w)) (hcoe a).symm`.
-/
theorem hasTh_classical : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (t : TObj g (N' ^ 2) J b (spMap em)) (u : HolUnif t.A t.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (lam : Fin (2 * g) → u.Λ), Odd N' → u.IsAH Hm χ → u.IsThetaFn Hm χ 1 θ → θ ≠ 0 → (∀ i, (t.pt i).left = (u.ex (((N' : ℂ) ^ 2)⁻¹ • (lam i : Fin g → ℂ))).left) → t.HasTh (𝟙 _) (fun a => χ (∑ i, ((a i).val : ℤ) • lam i) * Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * hermForm Hm (∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ)) (∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ))) * θ ((N' : ℂ)⁻¹ • ∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ))) := by
  intro hL hL2 hT o _ g N' J b em t u Hm χ θ lam hN hAH hθ h0 hpt
  have hN0 : (N' : ℂ) ≠ 0 := by exact_mod_cast hN.pos.ne'
  haveI := t.ab.comm
  refine ⟨hN, ?_, fun q => ⟨⊤, trivial, ?_⟩⟩
  · have h : IsUnit (N' : ℂ) := IsUnit.mk0 _ hN0
    have h' := h.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rw [map_natCast] at h'
    exact h'
  let T : Over (Sp ℂ) := Out.overRes (T := Out.baseOver (Sp ℂ)) ⊤
  haveI : IsIso T.hom := by
    show IsIso ((⊤ : (Sp ℂ).Opens).ι ≫ 𝟙 _)
    rw [Category.comp_id]
    exact inferInstanceAs (IsIso (Sp ℂ).topIso.hom)
  let p : 𝟙_ (Over (Sp ℂ)) ⟶ T := Over.homMk (inv T.hom) (by simp)
  have hp : p ≫ Out.overResι (T := Out.baseOver (Sp ℂ)) ⊤ = 𝟙 _ := by
    ext1
    show inv T.hom ≫ (⊤ : (Sp ℂ).Opens).ι = 𝟙 _
    rw [IsIso.inv_comp_eq]
    rfl
  have hpt' : t.pt = fun i => u.ex (((N' : ℂ) ^ 2)⁻¹ • (lam i : Fin g → ℂ)) :=
    funext fun i => Over.OverMorphism.ext (hpt i)
  have hcoe : ∀ a : Ix g (N' ^ 2), ((∑ i, ((a i).val : ℤ) • lam i : u.Λ) : Fin g → ℂ) =
      ∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ) := fun a => by
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, natCast_zsmul, Nat.cast_smul_eq_nsmul]
  have hlab : ∀ a : Ix g (N' ^ 2), t.lab a =
      u.ex (((N' : ℂ) ^ 2)⁻¹ • ((∑ i, ((a i).val : ℤ) • lam i : u.Λ) : Fin g → ℂ)) := fun a => by
    rw [hcoe, Finset.smul_sum, TObj.lab, hpt']
    refine (ex_sum u _ _).symm.trans (congrArg u.ex (Finset.sum_congr rfl fun i _ => ?_))
    rw [smul_comm, Nat.cast_smul_eq_nsmul]
  have htor : ∀ a : Ix g (N' ^ 2), t.lab a ^ (N' ^ 2) = 1 := fun a => by
    rw [TObj.lab, Out.linComb, List.prod_ofFn, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, t.torsion, one_pow]
  have key := isThetaPtOver hL hL2 hT t.pol u Hm χ θ N' T p
    (fun a : Ix g (N' ^ 2) => Out.overResι ⊤ ≫ t.lab a) (fun a => ∑ i, ((a i).val : ℤ) • lam i)
    hN hAH hθ h0 (fun a => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ t.lab a) hp).trans
      ((Category.id_comp _).trans (hlab a))))
    (fun a => exists_symLift hL t.pol (N' ^ 2) _ (by push_cast; rfl) hN.pow (t.lab a) (htor a))
  convert key using 2 with a a
  · congr 1
  · refine (constFn_top _).trans ?_
    refine congrArg (constFn T.hom ⊤) ?_
    exact congrArg (fun w : Fin g → ℂ => χ (∑ i, ((a i).val : ℤ) • lam i) *
      Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * hermForm Hm w w) * θ ((N' : ℂ)⁻¹ • w)) (hcoe a).symm

end GlobalTheory.ThetaClassical
