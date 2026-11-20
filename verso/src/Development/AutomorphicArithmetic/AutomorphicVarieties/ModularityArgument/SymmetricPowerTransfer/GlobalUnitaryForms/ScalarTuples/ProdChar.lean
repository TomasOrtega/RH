import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.IotaEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ChiProd

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

/- English proof (translation)
Establish `hc : ∀ z x, σ z * x = x * σ z` using `fun z x => (Subgroup.mem_center_iff.mp (hσ z) x).symm`. Establish `hmul : ∀ z z' a b, (σ z)⁻¹ * a ∈ J → (σ z')⁻¹ * b ∈ J → (σ (z * z'))⁻¹ * (a * b) ∈ J`. Introduce `z z' a b h h'`. Establish `hc' : (σ z')⁻¹ * ((σ z)⁻¹ * a) = ((σ z)⁻¹ * a) * (σ z')⁻¹`. Rewrite using `[← map_inv]`.

Conclude with `hc _ _`. Establish `e : (σ (z * z'))⁻¹ * (a * b) = ((σ z)⁻¹ * a) * ((σ z')⁻¹ * b)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul, _root_.mul_inv_rev]`. Use `group`.

Use `_ = ((σ z)⁻¹ * a) * (σ z')⁻¹ * b := by rw [hc']`. Use `_ = ((σ z)⁻¹ * a) * ((σ z')⁻¹ * b) := by group`. Rewrite using `[e]`. Conclude with `J.mul_mem h h'`. Set `S : Subgroup G` to `{ carrier := {u | ∃ z, (σ z)⁻¹ * u ∈ J} one_mem' := ⟨1, by simp⟩ mul_mem' := by`.

Introduce and unpack `a b ⟨z, hz⟩ ⟨z', hz'⟩`. Conclude with `⟨z * z', hmul _ _ _ _ hz hz'⟩`. Use the proof step `inv_mem' := by`. Introduce and unpack `a ⟨z, hz⟩`. Use `⟨z⁻¹, ?_⟩` and prove the remaining obligations.

Establish `h` using `J.inv_mem hz`. Rewrite `h` using `[_root_.mul_inv_rev, inv_inv, ← hc]`. Simplify `h }` using `[map_inv]`. Establish `hsup : σ.range ⊔ J ≤ S`. Use `sup_le ?_ ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `⟨z, by simp⟩`. Introduce `j hj`. Conclude with `⟨1, by simpa using hj⟩`. Establish `hS : ∀ u ∈ σ.range ⊔ J, ∃ z, (σ z)⁻¹ * u ∈ J` using `fun u hu => hsup hu`.

Establish `hwd : ∀ z z' x, (σ z)⁻¹ * x ∈ J → (σ z')⁻¹ * x ∈ J → χ z = χ z'`. Introduce `z z' x h h'`. Establish `hm` using `J.mul_mem h (J.inv_mem h')`. Establish `e : (σ z)⁻¹ * x * ((σ z')⁻¹ * x)⁻¹ = σ (z⁻¹ * z')`. Rewrite using `[map_mul, map_inv]`.

Use `group`. Rewrite `hm` using `[e]`. Establish `h2` using `hχ _ (hJ hm)`. Rewrite `h2` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `h2`.

Set `f : ↥(σ.range ⊔ J) → C` to `fun u => χ (Classical.choose (hS u.1 u.2))`. Establish `hf : ∀ (u : ↥(σ.range ⊔ J)) z, (σ z)⁻¹ * u.1 ∈ J → f u = χ z` using `fun u z h => hwd _ _ _ (Classical.choose_spec (hS u.1 u.2)) h`. Use `⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, hf, ?_⟩` and prove the remaining obligations. Conclude with `(hf 1 1 (by simp)).trans (map_one χ)`. Introduce `u v`.

Take `⟨z, hz⟩` from `hS u.1 u.2`. Take `⟨z', hz'⟩` from `hS v.1 v.2`. Use `show f (u * v) = f u * f v`. Rewrite using `[hf u z hz, hf v z' hz', hf (u * v) (z * z') (hmul _ _ _ _ hz hz'), map_mul]`. Introduce `u hu`.

Take `⟨z, hz⟩` from `hS u.1 u.2`. Use `show f u = 1`. Rewrite using `[hf u z hz]`. Apply `hχ` to reduce the goal to its premises. Establish `e : u.1 * ((σ z)⁻¹ * u.1)⁻¹ = σ z` using `by group`.

Rewrite using `[← e]`. Conclude with `Kg.mul_mem hu (Kg.inv_mem (hJ hz))`.
-/
private theorem ext_char {A G C : Type} [Group A] [Group G] [CommGroup C] (σ : A →* G)
    (hσ : ∀ z, σ z ∈ Subgroup.center G) (χ : A →* C) (J Kg : Subgroup G) (hJ : J ≤ Kg)
    (hχ : ∀ z, σ z ∈ Kg → χ z = 1) :
    ∃ ω : ↥(σ.range ⊔ J) →* C, (∀ u z, (σ z)⁻¹ * u.1 ∈ J → ω u = χ z) ∧ ∀ u, u.1 ∈ Kg → ω u = 1 := by
  classical
  have hc : ∀ z x, σ z * x = x * σ z := fun z x => (Subgroup.mem_center_iff.mp (hσ z) x).symm
  have hmul : ∀ z z' a b, (σ z)⁻¹ * a ∈ J → (σ z')⁻¹ * b ∈ J → (σ (z * z'))⁻¹ * (a * b) ∈ J := by
    intro z z' a b h h'
    have hc' : (σ z')⁻¹ * ((σ z)⁻¹ * a) = ((σ z)⁻¹ * a) * (σ z')⁻¹ := by
      rw [← map_inv]; exact hc _ _
    have e : (σ (z * z'))⁻¹ * (a * b) = ((σ z)⁻¹ * a) * ((σ z')⁻¹ * b) := by
      calc (σ (z * z'))⁻¹ * (a * b) = (σ z')⁻¹ * ((σ z)⁻¹ * a) * b := by
            rw [map_mul, _root_.mul_inv_rev]; group
        _ = ((σ z)⁻¹ * a) * (σ z')⁻¹ * b := by rw [hc']
        _ = ((σ z)⁻¹ * a) * ((σ z')⁻¹ * b) := by group
    rw [e]; exact J.mul_mem h h'
  let S : Subgroup G :=
    { carrier := {u | ∃ z, (σ z)⁻¹ * u ∈ J}
      one_mem' := ⟨1, by simp⟩
      mul_mem' := by
        rintro a b ⟨z, hz⟩ ⟨z', hz'⟩
        exact ⟨z * z', hmul _ _ _ _ hz hz'⟩
      inv_mem' := by
        rintro a ⟨z, hz⟩
        refine ⟨z⁻¹, ?_⟩
        have h := J.inv_mem hz
        rw [_root_.mul_inv_rev, inv_inv, ← hc] at h
        simpa [map_inv] using h }
  have hsup : σ.range ⊔ J ≤ S := by
    refine sup_le ?_ ?_
    · rintro _ ⟨z, rfl⟩
      exact ⟨z, by simp⟩
    · intro j hj
      exact ⟨1, by simpa using hj⟩
  have hS : ∀ u ∈ σ.range ⊔ J, ∃ z, (σ z)⁻¹ * u ∈ J := fun u hu => hsup hu
  have hwd : ∀ z z' x, (σ z)⁻¹ * x ∈ J → (σ z')⁻¹ * x ∈ J → χ z = χ z' := by
    intro z z' x h h'
    have hm := J.mul_mem h (J.inv_mem h')
    have e : (σ z)⁻¹ * x * ((σ z')⁻¹ * x)⁻¹ = σ (z⁻¹ * z') := by
      rw [map_mul, map_inv]; group
    rw [e] at hm
    have h2 := hχ _ (hJ hm)
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  let f : ↥(σ.range ⊔ J) → C := fun u => χ (Classical.choose (hS u.1 u.2))
  have hf : ∀ (u : ↥(σ.range ⊔ J)) z, (σ z)⁻¹ * u.1 ∈ J → f u = χ z :=
    fun u z h => hwd _ _ _ (Classical.choose_spec (hS u.1 u.2)) h
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, hf, ?_⟩
  · exact (hf 1 1 (by simp)).trans (map_one χ)
  · intro u v
    obtain ⟨z, hz⟩ := hS u.1 u.2
    obtain ⟨z', hz'⟩ := hS v.1 v.2
    show f (u * v) = f u * f v
    rw [hf u z hz, hf v z' hz', hf (u * v) (z * z') (hmul _ _ _ _ hz hz'), map_mul]
  · intro u hu
    obtain ⟨z, hz⟩ := hS u.1 u.2
    show f u = 1
    rw [hf u z hz]
    apply hχ
    have e : u.1 * ((σ z)⁻¹ * u.1)⁻¹ = σ z := by group
    rw [← e]
    exact Kg.mul_mem hu (Kg.inv_mem (hJ hz))

/- English proof (translation)
Establish `hmem : ∀ (u : (rpg Gv K).box U) v, u.1.1 v ∈ U v` using `fun u v => Subgroup.mem_iInf.mp u.2 v`. Set `g : (rpg Gv K).box U → I → ℂˣ` to `fun u v => w v ⟨u.1.1 v, hmem u v⟩`. Establish `hfin : ∀ u, (Function.mulSupport (g u)).Finite`. Introduce `u`. Establish `h` using `Filter.eventually_cofinite.mp ((rpg Gv K).ae u.1)`.

Use `h.subset ?_` and prove the remaining obligations. Introduce `v hv`. Assume the negation of the conclusion as `hK`. Conclude with `hv (hw v ⟨u.1.1 v, hmem u v⟩ (not_not.mp hK))`. Use `⟨{ toFun := fun u => ∏ᶠ v, g u v, map_one' := ?_, map_mul' := ?_ }, ?_⟩` and prove the remaining obligations.

Use `show ∏ᶠ v, g 1 v = 1`. Rewrite using `[show g 1 = fun _ => 1 from funext fun v => map_one (w v)]`. Conclude with `finprod_one`. Introduce `a b show ∏ᶠ v, g (a * b) v = (∏ᶠ v, g a v) * ∏ᶠ v, g b v`. Establish `e : g (a * b) = fun v => g a v * g b v`.

Use function extensionality and compare the values at `v`. Conclude with `map_mul (w v) ⟨a.1.1 v, hmem a v⟩ ⟨b.1.1 v, hmem b v⟩`. Rewrite using `[e]`. Conclude with `finprod_mul_distrib (hfin a) (hfin b)`. Introduce `u c hc show ((∏ᶠ v, g u v : ℂˣ) : ℂ) = ∏ᶠ v, (c v : ℂ)`.

Establish `e : g u = c` using `funext fun v => hc v (hmem u v)`. Rewrite using `[← e]`. Conclude with `MonoidHom.map_finprod (Units.coeHom ℂ) (hfin u)`.
-/
private theorem prod_char {I : Type} (Gv : I → Type) [∀ v, Group (Gv v)] (K U : ∀ v, Subgroup (Gv v))
    (w : ∀ v, U v →* ℂˣ) (hw : ∀ v u, u.1 ∈ K v → w v u = 1) :
    ∃ ω : (rpg Gv K).box U →* ℂˣ, ∀ (u : (rpg Gv K).box U) (c : I → ℂˣ),
      (∀ v (h : u.1.1 v ∈ U v), w v ⟨u.1.1 v, h⟩ = c v) → (ω u : ℂ) = ∏ᶠ v, (c v : ℂ) := by
  classical
  have hmem : ∀ (u : (rpg Gv K).box U) v, u.1.1 v ∈ U v := fun u v => Subgroup.mem_iInf.mp u.2 v
  let g : (rpg Gv K).box U → I → ℂˣ := fun u v => w v ⟨u.1.1 v, hmem u v⟩
  have hfin : ∀ u, (Function.mulSupport (g u)).Finite := by
    intro u
    have h := Filter.eventually_cofinite.mp ((rpg Gv K).ae u.1)
    refine h.subset ?_
    intro v hv
    by_contra hK
    exact hv (hw v ⟨u.1.1 v, hmem u v⟩ (not_not.mp hK))
  refine ⟨{ toFun := fun u => ∏ᶠ v, g u v, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · show ∏ᶠ v, g 1 v = 1
    rw [show g 1 = fun _ => 1 from funext fun v => map_one (w v)]
    exact finprod_one
  · intro a b
    show ∏ᶠ v, g (a * b) v = (∏ᶠ v, g a v) * ∏ᶠ v, g b v
    have e : g (a * b) = fun v => g a v * g b v := by
      funext v
      exact map_mul (w v) ⟨a.1.1 v, hmem a v⟩ ⟨b.1.1 v, hmem b v⟩
    rw [e]
    exact finprod_mul_distrib (hfin a) (hfin b)
  · intro u c hc
    show ((∏ᶠ v, g u v : ℂˣ) : ℂ) = ∏ᶠ v, (c v : ℂ)
    have e : g u = c := funext fun v => hc v (hmem u v)
    rw [← e]
    exact MonoidHom.map_finprod (Units.coeHom ℂ) (hfin u)

section Local

variable {K : Type} [Field K] (Δ : K)

/- English proof (translation)
Set `f : Kˣ →* GL (Fin 2) (Lsq K Δ)` to `(GeneralLinearGroup.scalar (Fin 2)).comp (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ))`. Establish `hfm : ∀ z, ((f z : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = Matrix.scalar (Fin 2) (algebraMap K (Lsq K Δ) z)` using `fun z => by simp [f]`. Establish `hcomm : ∀ z (g : GL (Fin 2) (Lsq K Δ)), f z * g = g * f z`. Introduce `z g`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Units.val_mul, Units.val_mul, hfm]`. Conclude with `(Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq`. Establish `hmem : ∀ z, f z ∈ DX Δ`. Introduce `z`. Use `show GeneralLinearGroup.map (starRingEnd _) (f z) = MulAut.conj (wJ Δ)⁻¹ (f z)`.

Rewrite using `[MulAut.conj_apply, ← hcomm, mul_assoc, mul_inv_cancel, mul_one]`. Apply `Units.ext` to reduce the goal to its premises. Use `show ((f z : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd _) = _`. Rewrite using `[hfm]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]`. Use `split_ifs`. Apply the tactic sequence `ext <;> simp [starRingEnd_apply]`. Simplify using the standard rewrite rules. Use `⟨f.codRestrict (DX Δ) hmem, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `z s`. Establish `e : (((f.codRestrict (DX Δ) hmem z : DX Δ) : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = Matrix.scalar (Fin 2) (algebraMap K (Lsq K Δ) z)` using `hfm z`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Conclude with `(show mt s = _ from h).trans e.symm`. Introduce and unpack `rfl`. Conclude with `e`. Use extensionality with `s`.

Rewrite using `[ZD, Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.mem_range]`. Use `exists_congr fun z => ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩` and prove the remaining obligations. Introduce `z`. Rewrite using `[Subgroup.mem_center_iff]`. Introduce `g`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show (g : GL (Fin 2) (Lsq K Δ)) * f z = f z * g`. Conclude with `(hcomm z g).symm`.
-/
private theorem scal_ex : ∃ σ : Kˣ →* DX Δ, (∀ z s, IsScal z s ↔ s = σ z) ∧ ZD Δ = σ.range ∧
    ∀ z, σ z ∈ Subgroup.center (DX Δ) := by
  classical
  let f : Kˣ →* GL (Fin 2) (Lsq K Δ) :=
    (GeneralLinearGroup.scalar (Fin 2)).comp (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ))
  have hfm : ∀ z, ((f z : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) =
      Matrix.scalar (Fin 2) (algebraMap K (Lsq K Δ) z) := fun z => by simp [f]
  have hcomm : ∀ z (g : GL (Fin 2) (Lsq K Δ)), f z * g = g * f z := by
    intro z g
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hfm]
    exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq
  have hmem : ∀ z, f z ∈ DX Δ := by
    intro z
    show GeneralLinearGroup.map (starRingEnd _) (f z) = MulAut.conj (wJ Δ)⁻¹ (f z)
    rw [MulAut.conj_apply, ← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    apply Units.ext
    show ((f z : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd _) = _
    rw [hfm]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · ext <;> simp [starRingEnd_apply]
    · simp
  refine ⟨f.codRestrict (DX Δ) hmem, ?_, ?_, ?_⟩
  · intro z s
    have e : (((f.codRestrict (DX Δ) hmem z : DX Δ) : GL (Fin 2) (Lsq K Δ)) :
        Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = Matrix.scalar (Fin 2) (algebraMap K (Lsq K Δ) z) := hfm z
    constructor
    · intro h
      apply Subtype.ext
      apply Units.ext
      exact (show mt s = _ from h).trans e.symm
    · rintro rfl
      exact e
  · ext s
    rw [ZD, Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.mem_range]
    refine exists_congr fun z => ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · intro z
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : GL (Fin 2) (Lsq K Δ)) * f z = f z * g
    exact (hcomm z g).symm

variable {Δ} {O : Type} [CommRing O] [Algebra O K]

/- English proof (translation)
Take `⟨g, hg⟩` from `MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hs)`. Establish `h1 : ((s : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0 = algebraMap K (Lsq K Δ) z`. Rewrite using `[show ((s : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = _ from h]`. Simplify using the standard rewrite rules. Establish `h2 : ((s : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0 = ((g : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ))) 0 0 : Lsq K Δ)`.

Rewrite using `[← hg]`. Both sides reduce to the same expression. Establish `h3 : IsIntegral O (algebraMap K (Lsq K Δ) z)`. Rewrite using `[← h1, h2]`. Conclude with `((g : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ))) 0 0).2`.

Conclude with `(isIntegral_algHom_iff (IsScalarTower.toAlgHom O K (Lsq K Δ)) (algebraMap K (Lsq K Δ)).injective).mp h3`.
-/
private theorem scal_int {z : Kˣ} {s : DX Δ} (h : IsScal z s) (hs : s ∈ KD Δ O) : IsIntegral O (z : K) := by
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hs)
  have h1 : ((s : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0 =
      algebraMap K (Lsq K Δ) z := by
    rw [show ((s : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = _ from h]
    simp
  have h2 : ((s : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0 =
      ((g : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ))) 0 0 : Lsq K Δ) := by
    rw [← hg]
    rfl
  have h3 : IsIntegral O (algebraMap K (Lsq K Δ) z) := by
    rw [← h1, h2]
    exact ((g : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ))) 0 0).2
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom O K (Lsq K Δ))
    (algebraMap K (Lsq K Δ)).injective).mp h3

/- English proof (translation)
Take `⟨σ, hs, hZ, hc⟩` from `scal_ex (K := K) Δ`. Establish `hχ' : ∀ z, σ z ∈ KD Δ O → χ z = 1`. Introduce `z hz`. Establish `hi : IsIntegral O (z : K)` using `scal_int ((hs z (σ z)).mpr rfl) hz`. Establish `hz' : σ z⁻¹ ∈ KD Δ O` using `by rw [map_inv]; exact (KD Δ O).inv_mem hz`.

Establish `hi' : IsIntegral O ((z⁻¹ : Kˣ) : K)` using `scal_int ((hs z⁻¹ (σ z⁻¹)).mpr rfl) hz'`. Take `⟨a, ha⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hi`. Take `⟨b, hb⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hi'`. Establish `hab : a * b = 1`. Apply `IsFractionRing.injective O K` to reduce the goal to its premises.

Rewrite using `[map_mul, ha, hb, map_one, Units.mul_inv]`. Set `u : Oˣ` to `⟨a, b, hab, by rw [mul_comm]; exact hab⟩`. Establish `hu : Units.map (algebraMap O K : O →* K) u = z` using `Units.ext ha`. Rewrite using `[← hu]`. Conclude with `hχ u`.

Rewrite using `[hZ]`. Take `⟨ω, h1, h2⟩` from `ext_char σ hc χ J (KD Δ O) hJ hχ'`. Use `⟨ω, ?_, h2⟩` and prove the remaining obligations. Introduce `u z s hzs hu`. Rewrite `hu` using `[(hs z s).mp hzs]`.

Conclude with `h1 u z hu`.
-/
private theorem loc_char [IsDomain O] [IsIntegrallyClosed O] [IsFractionRing O K] (χ : Kˣ →* ℂˣ) (hχ : Unr O χ)
    (J : Subgroup (DX Δ)) (hJ : J ≤ KD Δ O) :
    ∃ ω : ↥(ZD Δ ⊔ J) →* ℂˣ, (∀ u z s, IsScal z s → s⁻¹ * u.1 ∈ J → ω u = χ z) ∧ ∀ u, u.1 ∈ KD Δ O → ω u = 1 := by
  obtain ⟨σ, hs, hZ, hc⟩ := scal_ex (K := K) Δ
  have hχ' : ∀ z, σ z ∈ KD Δ O → χ z = 1 := by
    intro z hz
    have hi : IsIntegral O (z : K) := scal_int ((hs z (σ z)).mpr rfl) hz
    have hz' : σ z⁻¹ ∈ KD Δ O := by rw [map_inv]; exact (KD Δ O).inv_mem hz
    have hi' : IsIntegral O ((z⁻¹ : Kˣ) : K) := scal_int ((hs z⁻¹ (σ z⁻¹)).mpr rfl) hz'
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi'
    have hab : a * b = 1 := by
      apply IsFractionRing.injective O K
      rw [map_mul, ha, hb, map_one, Units.mul_inv]
    let u : Oˣ := ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
    have hu : Units.map (algebraMap O K : O →* K) u = z := Units.ext ha
    rw [← hu]
    exact hχ u
  rw [hZ]
  obtain ⟨ω, h1, h2⟩ := ext_char σ hc χ J (KD Δ O) hJ hχ'
  refine ⟨ω, ?_, h2⟩
  intro u z s hzs hu
  rw [(hs z s).mp hzs] at hu
  exact h1 u z hu

end Local

/- English proof (translation)
Introduce `F _ _ Δ D hD V _ _ W ch hW htr`. Take `⟨ιD, hιD⟩` from `(iotaEx F Δ).2.1`. Establish `hloc : ∀ v : Pl F, ∃ ω : ↥(ZD (cv v Δ) ⊔ D.J2v v) →* ℂˣ, (∀ u z s, IsScal z s → s⁻¹ * u.1 ∈ D.J2v v → ω u = D.χ v z) ∧ ∀ u, u.1 ∈ KD (cv v Δ) (Ov v) → ω u = 1`. Introduce `v`. Establish `hJ : D.J2v v ≤ KD (cv v Δ) (Ov v)`.

Unfold `Dat.J2v`. Use `split_ifs with hv`. Conclude with `(hD.sig v hv).levelTwoLeIntegral`. Conclude with `le_rfl`. Conclude with `loc_char (D.χ v) (hD.chi v).1 (D.J2v v) hJ`.

Use `choose w hw1 hw2 using hloc`. Take `⟨ω, hω⟩` from `prod_char (fun v => ↥(DX (cv v Δ))) (fun v => KD (cv v Δ) (Ov v)) (fun v => ZD (cv v Δ) ⊔ D.J2v v) w hw2`. Establish `hsc : ∀ (z0 : Fˣ) (s : DX Δ), IsScal z0 s → ∀ v, IsScal (Units.map (cv v : F →* Kv v) z0) ((ιD s : DA Δ).1 v)`. Introduce `z0 s hs v`. Use `show mt _ = _`.

Rewrite using `[hιD s v, show mt s = _ from hs]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]`. Use `split_ifs`. Apply the tactic sequence `ext <;> simp [lmap]`.

Simplify using the standard rewrite rules. Establish `hlocZ : ∀ v (z : (Kv v)ˣ) (s : DX (cv v Δ)), IsScal z s → s ∈ ZD (cv v Δ) ∧ s ∈ Subgroup.center (DX (cv v Δ))`. Introduce `v z s h`. Take `⟨σ, hs, hZ, hc⟩` from `scal_ex (K := Kv v) (cv v Δ)`. Rewrite using `[(hs z s).mp h, hZ]`.

Conclude with `⟨⟨z, rfl⟩, hc z⟩`. Take `⟨σ, hsF, hZ, hcF⟩` from `scal_ex (K := F) Δ`. Establish `hZs : ∀ z ∈ ZD Δ, ∃ z0 : Fˣ, IsScal z0 z`. Introduce `z hz`. Rewrite `hz` using `[hZ]`.

Take `⟨z0, rfl⟩` from `hz`. Conclude with `⟨z0, (hsF z0 _).mpr rfl⟩`. Establish `hmemU : ∀ z ∈ ZD Δ, ιD z ∈ D.UZ`. Introduce `z hz`. Take `⟨z0, h0⟩` from `hZs z hz`.

Use `Subgroup.mem_iInf.mpr fun v => ?_` and prove the remaining obligations. Use `show (ιD z : DA Δ).1 v ∈ ZD (cv v Δ) ⊔ D.J2v v`. Conclude with `Subgroup.mem_sup_left (hlocZ v _ _ (hsc z0 z h0 v)).1`. Establish `hωs : ∀ (z0 : Fˣ) (s : DX Δ) (h : IsScal z0 s) (hm : ιD s ∈ D.UZ), ((ω ⟨ιD s, hm⟩ : ℂˣ) : ℂ) = ((Algebra.norm ℚ (z0 : F) : ℚ) : ℂ)⁻¹`. Introduce `z0 s h hm`.

Rewrite using `[← chiProd F Δ D hD z0]`. Use `hω ⟨ιD s, hm⟩ (fun v => D.χ v (Units.map (cv v : F →* Kv v) z0)) ?_` and prove the remaining obligations. Introduce `v hv`. Use `hw1 v _ _ _ (hsc z0 s h v) ?_` and prove the remaining obligations. Rewrite using `[inv_mul_cancel]`.

Conclude with `(D.J2v v).one_mem`. Set `B : Base (DX Δ) (DA Δ) V` to `{ ι := ιD U := D.UZ ω := ω W := W Γ₀ := ZD Δ cenΓ := by`. Rewrite using `[hZ]`. Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `hcF z`.

Use `cenG := by`. Introduce `z hz`. Take `⟨z0, h0⟩` from `hZs z hz`. Rewrite using `[Subgroup.mem_center_iff]`. Introduce `g`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `v`. Conclude with `Subgroup.mem_center_iff.mp (hlocZ v _ _ (hsc z0 z h0 v)).2 (g.1 v)`. Use `memU := hmemU`. Use `scal := by`.

Introduce `z hz x`. Take `⟨z0, h0⟩` from `hZs z hz`. Rewrite using `[hW z0 z h0 x]`. Use `congr 1`. Conclude with `(hωs z0 z h0 _).symm }`.

Use `⟨B, ⟨hιD, rfl, ?_, rfl, htr⟩, rfl⟩` and prove the remaining obligations. Introduce `u z s hzs`. Conclude with `hω u (fun v => D.χ v (z v)) fun v hv => hw1 v _ (z v) (s v) (hzs v).1 (hzs v).2`.
-/
theorem baseK : BaseK := by
  intro F _ _ Δ D hD V _ _ W ch hW htr
  classical
  obtain ⟨ιD, hιD⟩ := (iotaEx F Δ).2.1
  have hloc : ∀ v : Pl F, ∃ ω : ↥(ZD (cv v Δ) ⊔ D.J2v v) →* ℂˣ,
      (∀ u z s, IsScal z s → s⁻¹ * u.1 ∈ D.J2v v → ω u = D.χ v z) ∧
      ∀ u, u.1 ∈ KD (cv v Δ) (Ov v) → ω u = 1 := by
    intro v
    have hJ : D.J2v v ≤ KD (cv v Δ) (Ov v) := by
      unfold Dat.J2v
      split_ifs with hv
      · exact (hD.sig v hv).levelTwoLeIntegral
      · exact le_rfl
    exact loc_char (D.χ v) (hD.chi v).1 (D.J2v v) hJ
  choose w hw1 hw2 using hloc
  obtain ⟨ω, hω⟩ := prod_char (fun v => ↥(DX (cv v Δ))) (fun v => KD (cv v Δ) (Ov v))
    (fun v => ZD (cv v Δ) ⊔ D.J2v v) w hw2
  have hsc : ∀ (z0 : Fˣ) (s : DX Δ), IsScal z0 s →
      ∀ v, IsScal (Units.map (cv v : F →* Kv v) z0) ((ιD s : DA Δ).1 v) := by
    intro z0 s hs v
    show mt _ = _
    rw [hιD s v, show mt s = _ from hs]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · ext <;> simp [lmap]
    · simp
  have hlocZ : ∀ v (z : (Kv v)ˣ) (s : DX (cv v Δ)), IsScal z s →
      s ∈ ZD (cv v Δ) ∧ s ∈ Subgroup.center (DX (cv v Δ)) := by
    intro v z s h
    obtain ⟨σ, hs, hZ, hc⟩ := scal_ex (K := Kv v) (cv v Δ)
    rw [(hs z s).mp h, hZ]
    exact ⟨⟨z, rfl⟩, hc z⟩
  obtain ⟨σ, hsF, hZ, hcF⟩ := scal_ex (K := F) Δ
  have hZs : ∀ z ∈ ZD Δ, ∃ z0 : Fˣ, IsScal z0 z := by
    intro z hz
    rw [hZ] at hz
    obtain ⟨z0, rfl⟩ := hz
    exact ⟨z0, (hsF z0 _).mpr rfl⟩
  have hmemU : ∀ z ∈ ZD Δ, ιD z ∈ D.UZ := by
    intro z hz
    obtain ⟨z0, h0⟩ := hZs z hz
    refine Subgroup.mem_iInf.mpr fun v => ?_
    show (ιD z : DA Δ).1 v ∈ ZD (cv v Δ) ⊔ D.J2v v
    exact Subgroup.mem_sup_left (hlocZ v _ _ (hsc z0 z h0 v)).1
  have hωs : ∀ (z0 : Fˣ) (s : DX Δ) (h : IsScal z0 s) (hm : ιD s ∈ D.UZ),
      ((ω ⟨ιD s, hm⟩ : ℂˣ) : ℂ) = ((Algebra.norm ℚ (z0 : F) : ℚ) : ℂ)⁻¹ := by
    intro z0 s h hm
    rw [← chiProd F Δ D hD z0]
    refine hω ⟨ιD s, hm⟩ (fun v => D.χ v (Units.map (cv v : F →* Kv v) z0)) ?_
    intro v hv
    refine hw1 v _ _ _ (hsc z0 s h v) ?_
    rw [inv_mul_cancel]
    exact (D.J2v v).one_mem
  let B : Base (DX Δ) (DA Δ) V :=
    { ι := ιD
      U := D.UZ
      ω := ω
      W := W
      Γ₀ := ZD Δ
      cenΓ := by
        rw [hZ]
        rintro _ ⟨z, rfl⟩
        exact hcF z
      cenG := by
        intro z hz
        obtain ⟨z0, h0⟩ := hZs z hz
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        funext v
        exact Subgroup.mem_center_iff.mp (hlocZ v _ _ (hsc z0 z h0 v)).2 (g.1 v)
      memU := hmemU
      scal := by
        intro z hz x
        obtain ⟨z0, h0⟩ := hZs z hz
        rw [hW z0 z h0 x]
        congr 1
        exact (hωs z0 z h0 _).symm }
  refine ⟨B, ⟨hιD, rfl, ?_, rfl, htr⟩, rfl⟩
  intro u z s hzs
  exact hω u (fun v => D.χ v (z v)) fun v hv => hw1 v _ (z v) (s v) (hzs v).1 (hzs v).2

end UpperTheory.V.Z.Sym.Glob
