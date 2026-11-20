import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.HomogExistsStatement

namespace ReciprocityTheory.Coh

namespace CohomologyFunctoriality₂

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

section HomLemmas

variable {R : Type u} [CommRing R] {A B C : Cx R}

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `y`. Use `Submodule.Quotient.induction_on _ y fun z => ?_` and prove the remaining obligations. Use `show Submodule.Quotient.mk (φ.Z n z) = Submodule.Quotient.mk (ψ.Z n z)`. Use `congr 1`.

Conclude with `Subtype.ext (h n z)`.
-/
theorem Hom.H_congr (φ ψ : Hom A B) (h : ∀ n x, φ.f n x = ψ.f n x) (n : ℕ) : φ.H n = ψ.H n := by
  apply LinearMap.ext
  intro y
  refine Submodule.Quotient.induction_on _ y fun z => ?_
  show Submodule.Quotient.mk (φ.Z n z) = Submodule.Quotient.mk (ψ.Z n z)
  congr 1
  exact Subtype.ext (h n z)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Hom.H_mk (φ : Hom A B) (n : ℕ) (z : A.Z n) :
    φ.H n (Submodule.Quotient.mk z) = Submodule.Quotient.mk (φ.Z n z) := rfl

/- English proof (translation)
Use `Submodule.Quotient.induction_on _ y fun z => ?_` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem Hom.H_comp (φ : Hom A B) (ψ : Hom B C) (n : ℕ) (y : A.H n) :
    (ψ.comp φ).H n y = ψ.H n (φ.H n y) := by
  refine Submodule.Quotient.induction_on _ y fun z => ?_
  rfl

/- English proof (translation)
Use `Submodule.Quotient.induction_on _ y fun z => ?_` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem Hom.H_id (n : ℕ) (y : A.H n) : (Hom.id A).H n y = y := by
  refine Submodule.Quotient.induction_on _ y fun z => ?_
  rfl

/- English proof (translation)
Use `Submodule.Quotient.induction_on _ y fun z => ?_` and prove the remaining obligations. Use `show Submodule.Quotient.mk (φ.Z n z) = k • Submodule.Quotient.mk z`. Rewrite using `[← Submodule.Quotient.mk_smul]`. Use `congr 1`. Conclude with `Subtype.ext (h z)`.
-/
theorem Hom.H_nsmul (φ : Hom A A) (k : ℕ) (n : ℕ) (h : ∀ x, φ.f n x = k • x) (y : A.H n) :
    φ.H n y = k • y := by
  refine Submodule.Quotient.induction_on _ y fun z => ?_
  show Submodule.Quotient.mk (φ.Z n z) = k • Submodule.Quotient.mk z
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext (h z)

/- English proof (translation)
Use `Submodule.Quotient.induction_on _ y fun z => ?_` and prove the remaining obligations. Use `show Submodule.Quotient.mk (φ.Z n z) = ∑ c ∈ s, Submodule.Quotient.mk ((ψ c).Z n z)`. Rewrite using `[← Submodule.mkQ_apply, show (∑ c ∈ s, Submodule.Quotient.mk ((ψ c).Z n z) : B.H n) = ∑ c ∈ s, (Submodule.mkQ _) ((ψ c).Z n z) from rfl, ← map_sum]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[Submodule.coe_sum]`. Conclude with `h z.1`.
-/
theorem Hom.H_sum {ι : Type*} (s : Finset ι) (φ : Hom A B) (ψ : ι → Hom A B) (n : ℕ)
    (h : ∀ x, φ.f n x = ∑ c ∈ s, (ψ c).f n x) (y : A.H n) :
    φ.H n y = ∑ c ∈ s, (ψ c).H n y := by
  refine Submodule.Quotient.induction_on _ y fun z => ?_
  show Submodule.Quotient.mk (φ.Z n z) = ∑ c ∈ s, Submodule.Quotient.mk ((ψ c).Z n z)
  rw [← Submodule.mkQ_apply, show (∑ c ∈ s, Submodule.Quotient.mk ((ψ c).Z n z) : B.H n) =
    ∑ c ∈ s, (Submodule.mkQ _) ((ψ c).Z n z) from rfl, ← map_sum]
  congr 1
  apply Subtype.ext
  rw [Submodule.coe_sum]
  exact h z.1

end HomLemmas

section Retr

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)

/- English proof (translation)
Rewrite using `[Quotient.eq, QuotientGroup.rightRel_apply]`.
-/
theorem mkR_eq {a b : G} :
    Quotient.mk (QuotientGroup.rightRel U) a = Quotient.mk _ b ↔ b * a⁻¹ ∈ U := by
  rw [Quotient.eq, QuotientGroup.rightRel_apply]

/- English proof (translation)
Unfold `rep`. Rewrite using `[show Quotient.mk (QuotientGroup.rightRel U) ((x : G) * g) = Quotient.mk _ g from (mkR_eq U).2 (by simpa [mul_inv_rev, mul_assoc] using U.inv_mem x.2)]`.
-/
theorem rep_mul (x : U) (g : G) : rep U ((x : G) * g) = rep U g := by
  unfold rep
  rw [show Quotient.mk (QuotientGroup.rightRel U) ((x : G) * g) = Quotient.mk _ g from
    (mkR_eq U).2 (by simpa [mul_inv_rev, mul_assoc] using U.inv_mem x.2)]

/- English proof (translation)
Unfold `rep`. Rewrite using `[Quotient.out_eq]`.
-/
theorem rep_out (c : Quotient (QuotientGroup.rightRel U)) : rep U c.out = c.out := by
  unfold rep
  rw [Quotient.out_eq]

/- English proof (translation)
Unfold `rep`. Conclude with `Quotient.out_eq _`.
-/
theorem mk_rep (g : G) : (Quotient.mk (QuotientGroup.rightRel U) (rep U g)) = Quotient.mk _ g := by
  unfold rep
  exact Quotient.out_eq _

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [retr, rep_mul, Subgroup.coe_mul, mul_assoc]`.
-/
theorem retr_mul (x : U) (g : G) : retr U ((x : G) * g) = x * retr U g := by
  apply Subtype.ext
  simp only [retr, rep_mul, Subgroup.coe_mul, mul_assoc]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [retr, rep_out, mul_inv_cancel, OneMemClass.coe_one]`.
-/
theorem retr_out (c : Quotient (QuotientGroup.rightRel U)) : retr U c.out = 1 := by
  apply Subtype.ext
  simp only [retr, rep_out, mul_inv_cancel, OneMemClass.coe_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem retr_spec (g : G) : (retr U g : G) = g * (rep U g)⁻¹ := rfl

/- English proof (translation)
Use `continuous_iff_continuousAt.2 fun x => ?_` and prove the remaining obligations. Establish `hn : (fun y => y * x⁻¹) ⁻¹' (U : Set G) ∈ nhds x`. Use `(hU.preimage (continuous_mul_const _)).mem_nhds ?_` and prove the remaining obligations. Simplify using `[U.one_mem]`. Use `(continuousAt_const (y := rep U x)).congr ?_` and prove the remaining obligations.

Use `filter_upwards [hn] with y hy`. Establish `: y = ((⟨y * x⁻¹, hy⟩ : U) : G) * x` using `by simp`. Rewrite using `[this, rep_mul]`.
-/
theorem continuous_rep (hU : IsOpen (U : Set G)) : Continuous (rep U) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hn : (fun y => y * x⁻¹) ⁻¹' (U : Set G) ∈ nhds x := by
    refine (hU.preimage (continuous_mul_const _)).mem_nhds ?_
    simp [U.one_mem]
  refine (continuousAt_const (y := rep U x)).congr ?_
  filter_upwards [hn] with y hy
  have : y = ((⟨y * x⁻¹, hy⟩ : U) : G) * x := by simp
  rw [this, rep_mul]

/- English proof (translation)
The claim follows from `(continuous_id.mul ((continuous_rep U hU).inv)).subtype_mk _`.
-/
theorem continuous_retr (hU : IsOpen (U : Set G)) : Continuous (retr U) :=
  (continuous_id.mul ((continuous_rep U hU).inv)).subtype_mk _

instance finite_rightRel [U.FiniteIndex] : Finite (Quotient (QuotientGroup.rightRel U)) :=
  Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel U).symm

/- English proof (translation)
Rewrite using `[Subgroup.index, ← Nat.card_eq_fintype_card]`. Conclude with `Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel U)`.
-/
theorem card_rightRel [U.FiniteIndex] [Fintype (Quotient (QuotientGroup.rightRel U))] :
    Fintype.card (Quotient (QuotientGroup.rightRel U)) = U.index := by
  rw [Subgroup.index, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel U)

def cosetMul (g : G) (c : Quotient (QuotientGroup.rightRel U)) : Quotient (QuotientGroup.rightRel U) :=
  Quotient.mk _ (c.out * g)

/- English proof (translation)
Establish `key : ∀ y : G, Quotient.mk (QuotientGroup.rightRel U) ((Quotient.mk (QuotientGroup.rightRel U) y).out * g) = Quotient.mk _ (y * g)`. Introduce `y`. Rewrite using `[mkR_eq]`. Establish `h1 : (Quotient.mk (QuotientGroup.rightRel U) y).out = rep U y` using `rfl`. Establish `h2 : y * (rep U y)⁻¹ ∈ U` using `mul_rep_inv_mem U y`.

Rewrite using `[h1]`. Simplify `h2` using `[mul_inv_rev, mul_assoc]`. Prove the components needed by the constructor for the conclusion. Introduce `c d hcd`. Unfold `cosetMul at hcd`.

Rewrite `hcd` using `[mkR_eq]`. Establish `h : d.out * c.out⁻¹ ∈ U` using `by simpa [mul_inv_rev, mul_assoc] using hcd`. Rewrite using `[← Quotient.out_eq c, ← Quotient.out_eq d]`. Conclude with `(mkR_eq U).2 h`. Introduce `d`.

Use `⟨Quotient.mk _ (d.out * g⁻¹), ?_⟩` and prove the remaining obligations. Unfold `cosetMul`. Rewrite using `[key, mul_assoc, inv_mul_cancel, mul_one, Quotient.out_eq]`.
-/
theorem cosetMul_bij (g : G) : Bijective (cosetMul U g) := by
  have key : ∀ y : G, Quotient.mk (QuotientGroup.rightRel U)
      ((Quotient.mk (QuotientGroup.rightRel U) y).out * g) = Quotient.mk _ (y * g) := by
    intro y
    rw [mkR_eq]
    have h1 : (Quotient.mk (QuotientGroup.rightRel U) y).out = rep U y := rfl
    have h2 : y * (rep U y)⁻¹ ∈ U := mul_rep_inv_mem U y
    rw [h1]
    simpa [mul_inv_rev, mul_assoc] using h2
  constructor
  · intro c d hcd
    unfold cosetMul at hcd
    rw [mkR_eq] at hcd
    have h : d.out * c.out⁻¹ ∈ U := by simpa [mul_inv_rev, mul_assoc] using hcd
    rw [← Quotient.out_eq c, ← Quotient.out_eq d]
    exact (mkR_eq U).2 h
  · intro d
    refine ⟨Quotient.mk _ (d.out * g⁻¹), ?_⟩
    unfold cosetMul
    rw [key, mul_assoc, inv_mul_cancel, mul_one, Quotient.out_eq]

/- English proof (translation)
Use `show c.out * g = (c.out * g) * (rep U (c.out * g))⁻¹ * (Quotient.mk _ (c.out * g)).out`. Unfold `rep`. Use `group`.
-/
theorem out_mul (g : G) (c : Quotient (QuotientGroup.rightRel U)) :
    c.out * g = (retr U (c.out * g) : G) * (cosetMul U g c).out := by
  show c.out * g = (c.out * g) * (rep U (c.out * g))⁻¹ * (Quotient.mk _ (c.out * g)).out
  unfold rep
  group

end Retr

section Norm

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : TRep R G) (U : Subgroup G) [U.FiniteIndex]

def normF (n : ℕ) (F : (Fin (n + 1) → G) → M.V) (x : Fin (n + 1) → G) : M.V :=
  ∑ᶠ c : Quotient (QuotientGroup.rightRel U), M.rho c.out⁻¹ (F fun i => c.out * x i)

/- English proof (translation)
Unfold `normF`. Conclude with `finsum_eq_sum_of_fintype _`.
-/
theorem normF_eq [Fintype (Quotient (QuotientGroup.rightRel U))] (n : ℕ) (F : (Fin (n + 1) → G) → M.V)
    (x : Fin (n + 1) → G) :
    normF M U n F x = ∑ c : Quotient (QuotientGroup.rightRel U), M.rho c.out⁻¹ (F fun i => c.out * x i) := by
  unfold normF
  exact finsum_eq_sum_of_fintype _

/- English proof (translation)
The claim follows from `M.cont.comp (continuous_const.prodMk continuous_id)`.
-/
theorem continuous_rho (s : G) : Continuous (M.rho s) :=
  M.cont.comp (continuous_const.prodMk continuous_id)

/- English proof (translation)
Use `haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _`. Use `⟨?_, fun g x => ?_⟩` and prove the remaining obligations. Establish `: normF M U n F = fun x => ∑ c : Quotient (QuotientGroup.rightRel U), M.rho c.out⁻¹ (F fun i => c.out * x i)` using `funext (normF_eq M U n F)`. Rewrite using `[this]`. Use `continuous_finset_sum _ fun c _ => (continuous_rho M _).comp (hF.1.comp ?_)` and prove the remaining obligations.

Conclude with `continuous_pi fun i => continuous_const.mul (continuous_apply i)`. Rewrite using `[normF_eq, normF_eq, map_sum]`. Establish `key : ∀ c : Quotient (QuotientGroup.rightRel U), M.rho c.out⁻¹ (F fun i => c.out * (g • x i)) = M.rho g (M.rho (cosetMul U g c).out⁻¹ (F fun i => (cosetMul U g c).out * x i))`. Introduce `c`. Establish `e` using `out_mul U g c`.

Establish `h1 : (fun i => c.out * (g • x i)) = fun i => retr U (c.out * g) • ((cosetMul U g c).out * x i)`. Use function extensionality and compare the values at `i`. Use `show c.out * (g * x i) = (retr U (c.out * g) : G) * ((cosetMul U g c).out * x i)`. Rewrite using `[← mul_assoc, ← mul_assoc, ← e]`. Rewrite using `[h1, hF.2]`.

Use `show M.rho c.out⁻¹ (M.rho (retr U (c.out * g) : G) _) = _`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Use `congr 2`. Rewrite using `[show (retr U (c.out * g) : G) = c.out * g * ((cosetMul U g c).out)⁻¹ by`. Rewrite using `[eq_mul_inv_iff_mul_eq]`.

Conclude with `e.symm]`. Use `group`. Simplify using `only [key]`. Conclude with `Fintype.sum_bijective _ (cosetMul_bij U g) _ _ fun _ => rfl`.
-/
theorem normF_mem (n : ℕ) (F : (Fin (n + 1) → G) → M.V) (hF : F ∈ hcoch (M.resSub U) G n) :
    normF M U n F ∈ hcoch M G n := by
  classical
  haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
  refine ⟨?_, fun g x => ?_⟩
  · have : normF M U n F = fun x => ∑ c : Quotient (QuotientGroup.rightRel U),
        M.rho c.out⁻¹ (F fun i => c.out * x i) := funext (normF_eq M U n F)
    rw [this]
    refine continuous_finset_sum _ fun c _ => (continuous_rho M _).comp (hF.1.comp ?_)
    exact continuous_pi fun i => continuous_const.mul (continuous_apply i)
  · rw [normF_eq, normF_eq, map_sum]
    have key : ∀ c : Quotient (QuotientGroup.rightRel U),
        M.rho c.out⁻¹ (F fun i => c.out * (g • x i)) =
        M.rho g (M.rho (cosetMul U g c).out⁻¹ (F fun i => (cosetMul U g c).out * x i)) := by
      intro c
      have e := out_mul U g c
      have h1 : (fun i => c.out * (g • x i)) =
          fun i => retr U (c.out * g) • ((cosetMul U g c).out * x i) := by
        funext i
        show c.out * (g * x i) = (retr U (c.out * g) : G) * ((cosetMul U g c).out * x i)
        rw [← mul_assoc, ← mul_assoc, ← e]
      rw [h1, hF.2]
      show M.rho c.out⁻¹ (M.rho (retr U (c.out * g) : G) _) = _
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      rw [show (retr U (c.out * g) : G) = c.out * g * ((cosetMul U g c).out)⁻¹ by
        rw [eq_mul_inv_iff_mul_eq]; exact e.symm]
      group
    simp only [key]
    exact Fintype.sum_bijective _ (cosetMul_bij U g) _ _ fun _ => rfl

/- English proof (translation)
Use `haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _`. Use function extensionality and compare the values at `x`. Simplify using `only [normF_eq, hd, map_sum, map_zsmul, Finset.smul_sum]`. Conclude with `Finset.sum_comm`.
-/
theorem normF_hd (n : ℕ) (F : (Fin (n + 1) → G) → M.V) :
    normF M U (n + 1) (hd n F) = hd n (normF M U n F) := by
  classical
  haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
  funext x
  simp only [normF_eq, hd, map_sum, map_zsmul, Finset.smul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Use `haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _`. Use function extensionality and compare the values at `x`. Simplify using `only [Pi.add_apply, normF_eq, map_add, Finset.sum_add_distrib]`.
-/
theorem normF_add (n : ℕ) (F F' : (Fin (n + 1) → G) → M.V) :
    normF M U n (F + F') = normF M U n F + normF M U n F' := by
  classical
  haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
  funext x
  simp only [Pi.add_apply, normF_eq, map_add, Finset.sum_add_distrib]

/- English proof (translation)
Use `haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _`. Use function extensionality and compare the values at `x`. Simplify using `only [Pi.smul_apply, normF_eq, map_smul, Finset.smul_sum]`.
-/
theorem normF_smul (n : ℕ) (r : R) (F : (Fin (n + 1) → G) → M.V) :
    normF M U n (r • F) = r • normF M U n F := by
  classical
  haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
  funext x
  simp only [Pi.smul_apply, normF_eq, map_smul, Finset.smul_sum]

def normL (n : ℕ) : hcoch (M.resSub U) G n →ₗ[R] hcoch M G n where
  toFun F := ⟨normF M U n F.1, normF_mem M U n F.1 F.2⟩
  map_add' F F' := by
    classical
    haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
    refine Subtype.ext (funext fun x => ?_)
    exact congrFun (normF_add M U n F.1 F'.1) x
  map_smul' r F := by
    classical
    haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
    refine Subtype.ext (funext fun x => ?_)
    exact congrFun (normF_smul M U n r F.1) x

variable {M U}

def normCx (A : Cx R) (eA : ∀ n, A.X n ≃ₗ[R] hcoch (M.resSub U) G n) (hA : IsHomog (M.resSub U) G A eA)
    (eG : ∀ n, M.coch.X n ≃ₗ[R] hcoch M G n) (hG : IsHomog M G M.coch eG) : Hom A M.coch where
  f n := ((eG n).symm.toLinearMap.comp (normL M U n)).comp (eA n).toLinearMap
  comm n F := by
    apply (eG (n + 1)).injective
    apply Subtype.ext
    rw [hG]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    show normF M U (n + 1) (eA (n + 1) (A.d n F)).1 = hd n (normF M U n (eA n F).1)
    rw [hA]; exact normF_hd M U n _

/- English proof (translation)
Use `show (eG n ((eG n).symm (normL M U n (eA n F)))).1 = _`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Both sides reduce to the same expression.
-/
theorem normCx_spec (A : Cx R) (eA : ∀ n, A.X n ≃ₗ[R] hcoch (M.resSub U) G n)
    (hA : IsHomog (M.resSub U) G A eA) (eG : ∀ n, M.coch.X n ≃ₗ[R] hcoch M G n) (hG : IsHomog M G M.coch eG)
    (n : ℕ) (F : A.X n) : (eG n ((normCx A eA hA eG hG).f n F)).1 = normF M U n (eA n F).1 := by
  show (eG n ((eG n).symm (normL M U n (eA n F)))).1 = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end Norm

section Incl

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : TRep R G} {U : Subgroup G}

def inclL (n : ℕ) : hcoch M G n →ₗ[R] hcoch (M.resSub U) G n where
  toFun F := ⟨F.1, F.2.1, fun g x => F.2.2 g x⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def inclCx (A : Cx R) (eA : ∀ n, A.X n ≃ₗ[R] hcoch (M.resSub U) G n) (hA : IsHomog (M.resSub U) G A eA)
    (eG : ∀ n, M.coch.X n ≃ₗ[R] hcoch M G n) (hG : IsHomog M G M.coch eG) : Hom M.coch A where
  f n := ((eA n).symm.toLinearMap.comp (inclL n)).comp (eG n).toLinearMap
  comm n F := by
    apply (eA (n + 1)).injective
    apply Subtype.ext
    rw [hA]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    show (eG (n + 1) (M.coch.d n F)).1 = _
    rw [hG]; rfl

/- English proof (translation)
Use `show (eA n ((eA n).symm (inclL n (eG n F)))).1 = _`. Rewrite using `[LinearEquiv.apply_symm_apply]`. Both sides reduce to the same expression.
-/
theorem inclCx_spec (A : Cx R) (eA : ∀ n, A.X n ≃ₗ[R] hcoch (M.resSub U) G n)
    (hA : IsHomog (M.resSub U) G A eA) (eG : ∀ n, M.coch.X n ≃ₗ[R] hcoch M G n) (hG : IsHomog M G M.coch eG)
    (n : ℕ) (F : M.coch.X n) : (eA n ((inclCx A eA hA eG hG).f n F)).1 = (eG n F).1 := by
  show (eA n ((eA n).symm (inclL n (eG n F)))).1 = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end Incl

section Conj

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def conjHom (N : Subgroup G) [N.Normal] (s : G) : N →* N where
  toFun g := ⟨s⁻¹ * g * s, by simpa using Subgroup.Normal.conj_mem inferInstance _ g.2 s⁻¹⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

def conjPrime₂ (M : TRep R G) (N : Subgroup G) [N.Normal] (s : G) : Pair (M.resSub N) (M.resSub N) where
  φ := conjHom N s
  u := M.rho s
  φ_cont := by
    refine continuous_induced_rng.2 ?_
    show Continuous fun g : N => s⁻¹ * (g : G) * s
    fun_prop
  u_cont := continuous_rho M s
  equiv g m := by
    change (M.rho s * M.rho (s⁻¹ * ↑g * s)) m = (M.rho ↑g * M.rho s) m
    rw [← map_mul, ← map_mul]
    congr 2; group

/- English proof (translation)
Proceed by induction on `j using Fin.induction with`. Consider the case `zero => simp [Fin.partialProd_zero]`. Consider the case `succ j ih => simp [Fin.partialProd_succ, ih]`.
-/
theorem partialProd_coe {N : Subgroup G} {n : ℕ} (g : Fin n → N) (j : Fin (n + 1)) :
    Fin.partialProd (fun i => (g i : G)) j = ((Fin.partialProd g j : N) : G) := by
  induction j using Fin.induction with
  | zero => simp [Fin.partialProd_zero]
  | succ j ih => simp [Fin.partialProd_succ, ih]

/- English proof (translation)
Rewrite using `[retr_spec]`. Unfold `rep`. Rewrite using `[show Quotient.mk (QuotientGroup.rightRel N) (s * h) = Quotient.mk _ s from (mkR_eq N).2 (by`. Establish `h1` using `(inferInstance : N.Normal).conj_mem _ (N.inv_mem hh) s`. Simplify `h1)]` using `[mul_inv_rev, mul_assoc]`.
-/
theorem retr_conj (N : Subgroup G) [N.Normal] (s h : G) (hh : h ∈ N) :
    (retr N (s * h) : G) = s * h * (rep N s)⁻¹ := by
  rw [retr_spec]
  unfold rep
  rw [show Quotient.mk (QuotientGroup.rightRel N) (s * h) = Quotient.mk _ s from (mkR_eq N).2 (by
    have h1 := (inferInstance : N.Normal).conj_mem _ (N.inv_mem hh) s
    simpa [mul_inv_rev, mul_assoc] using h1)]

end Conj
end

end CohomologyFunctoriality₂

end ReciprocityTheory.Coh
