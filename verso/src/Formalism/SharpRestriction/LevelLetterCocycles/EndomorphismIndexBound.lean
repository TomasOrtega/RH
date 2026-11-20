import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.CharacterColumnKernels.Assemble
import Formalism.CharacterColumnKernels.IdempotentNormalForms.CongMem
import Formalism.CharacterColumnKernels.IdempotentNormalForms.CharacterColumnKernelsOfBlockChiCOfBlockChiOne
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaDetPoly
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.BridgeDet
import Formalism.CharacterColumnKernels.IdempotentNormalForms.IsUnitDetOfConst
import Formalism.CharacterColumnKernels.StatLowestInZ
import Formalism.CharacterColumnKernels.IdempotentNormalForms.CharacterColumnKernelLengthBound
import Formalism.CharacterColumnKernels.IdempotentNormalForms.MemCcIdealIffForall
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SumIteLe
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SplitFibre
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SpacedProductLowerBound
import Formalism.CharacterColumnKernels.IdempotentNormalForms.IdemNormalForm
import Mathlib
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SmulEqZeroIffCrit

noncomputable section

open Module IsDiscreteValuationRing Formalism.BasicNotions

namespace Formalism.MainNotions.TruncatedSeriesCountingIdentities

namespace Br

section Quot

variable {O : Type*} [CommRing O] {V : Type*} [AddCommGroup V] [Module O V]

/- English proof (translation)
Establish `hmem : ∀ v : ↥L, P v ∈ (L ⊔ B) ⊓ A`. Introduce `v`. Use `Submodule.mem_inf.mpr ⟨?_, hPA v⟩` and prove the remaining obligations. Establish `h1 : (v : V) ∈ L ⊔ B` using `Submodule.mem_sup_left v.2`. Establish `h2 : (v : V) - P v ∈ L ⊔ B` using `Submodule.mem_sup_right (hPB v)`.

Establish `h3` using `Submodule.sub_mem _ h1 h2`. Simplify using `using h3`. Set `g : ↥L →ₗ[O] ↥((L ⊔ B) ⊓ A)` to `LinearMap.codRestrict ((L ⊔ B) ⊓ A) (P ∘ₗ L.subtype) hmem`. Set `q` to `(Submodule.mkQ ((L ⊓ A).comap ((L ⊔ B) ⊓ A).subtype)) ∘ₗ g`. Establish `hK : ((A ⊓ L) ⊔ (B ⊓ L)).comap L.subtype ≤ LinearMap.ker q`.

Introduce `v hv`. Rewrite `hv` using `[Submodule.mem_comap]`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp hv`. Rewrite using `[LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Use `show P v ∈ L ⊓ A`.

Establish `hv' : (v : V) = a + b` using `hab.symm`. Rewrite using `[hv', map_add, hA a (Submodule.mem_inf.mp ha).1, hB b (Submodule.mem_inf.mp hb).1, add_zero]`. Conclude with `Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp ha).2, (Submodule.mem_inf.mp ha).1⟩`. Establish `hq : Function.Surjective q`. Introduce `y`.

Take `⟨w, rfl⟩` from `Submodule.mkQ_surjective _ y`. Take `⟨hwLB, hwA⟩` from `Submodule.mem_inf.mp w.2`. Take `⟨l, hl, b, hb, hlb⟩` from `Submodule.mem_sup.mp hwLB`. Use `⟨⟨l, hl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show P l = (w : V)`. Establish `hPw : P (w : V) = w` using `hA w hwA`. Rewrite using `[← hPw, ← hlb, map_add, hB b hb, add_zero]`.

Use `Module.length_le_of_surjective (Submodule.liftQ _ q hK) ?_` and prove the remaining obligations. Introduce `y`. Take `⟨v, rfl⟩` from `hq y`. Conclude with `⟨Submodule.Quotient.mk v, Submodule.liftQ_apply _ _ _⟩`.
-/
theorem quot_le (L A B : Submodule O V) (P : V →ₗ[O] V) (hA : ∀ v ∈ A, P v = v)
    (hB : ∀ v ∈ B, P v = 0) (hPA : ∀ v, P v ∈ A) (hPB : ∀ v, v - P v ∈ B) :
    Module.length O (↥((L ⊔ B) ⊓ A) ⧸ (L ⊓ A).comap ((L ⊔ B) ⊓ A).subtype) ≤
      Module.length O (↥L ⧸ ((A ⊓ L) ⊔ (B ⊓ L)).comap L.subtype) := by
  have hmem : ∀ v : ↥L, P v ∈ (L ⊔ B) ⊓ A := by
    intro v
    refine Submodule.mem_inf.mpr ⟨?_, hPA v⟩
    have h1 : (v : V) ∈ L ⊔ B := Submodule.mem_sup_left v.2
    have h2 : (v : V) - P v ∈ L ⊔ B := Submodule.mem_sup_right (hPB v)
    have h3 := Submodule.sub_mem _ h1 h2
    simpa using h3
  let g : ↥L →ₗ[O] ↥((L ⊔ B) ⊓ A) := LinearMap.codRestrict ((L ⊔ B) ⊓ A) (P ∘ₗ L.subtype) hmem
  let q := (Submodule.mkQ ((L ⊓ A).comap ((L ⊔ B) ⊓ A).subtype)) ∘ₗ g
  have hK : ((A ⊓ L) ⊔ (B ⊓ L)).comap L.subtype ≤ LinearMap.ker q := by
    intro v hv
    rw [Submodule.mem_comap] at hv
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    show P v ∈ L ⊓ A
    have hv' : (v : V) = a + b := hab.symm
    rw [hv', map_add, hA a (Submodule.mem_inf.mp ha).1, hB b (Submodule.mem_inf.mp hb).1, add_zero]
    exact Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp ha).2, (Submodule.mem_inf.mp ha).1⟩
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨hwLB, hwA⟩ := Submodule.mem_inf.mp w.2
    obtain ⟨l, hl, b, hb, hlb⟩ := Submodule.mem_sup.mp hwLB
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [LinearMap.comp_apply]
    congr 1
    apply Subtype.ext
    show P l = (w : V)
    have hPw : P (w : V) = w := hA w hwA
    rw [← hPw, ← hlb, map_add, hB b hb, add_zero]
  refine Module.length_le_of_surjective (Submodule.liftQ _ q hK) ?_
  intro y
  obtain ⟨v, rfl⟩ := hq y
  exact ⟨Submodule.Quotient.mk v, Submodule.liftQ_apply _ _ _⟩

end Quot

section Bump

variable {O : Type*} [CommRing O] [IsDomain O] {X : Type*} [Fintype X] [DecidableEq X]
  (T : Subalgebra O (X → O))

/- English proof (translation)
Use `first`. Consider the case `rw [SubmonoidClass.coe_finsetProd, Finset.prod_apply]`. Consider the case `simp [Finset.prod_apply]`.
-/
theorem coe_prod' {ι : Type*} (s : Finset ι) (h : ι → T) (z : X) :
    ((∏ y ∈ s, h y : T) : X → O) z = ∏ y ∈ s, ((h y : T) : X → O) z := by
  first
  | rw [SubmonoidClass.coe_finsetProd, Finset.prod_apply]
  | simp [Finset.prod_apply]

/- English proof (translation)
Use `first`. Consider the case `rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]`. Consider the case `simp [Finset.sum_apply]`.
-/
theorem coe_sum' {ι : Type*} (s : Finset ι) (h : ι → T) (z : X) :
    ((∑ y ∈ s, h y : T) : X → O) z = ∑ y ∈ s, ((h y : T) : X → O) z := by
  first
  | rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
  | simp [Finset.sum_apply]

/- English proof (translation)
Use `choose f hfT hf using fun y : {y : X // y ≠ x} => hsep x y.1 (Ne.symm y.2)`. Set `h : {y : X // y ≠ x} → T` to `fun y => ⟨f y, hfT y⟩ - algebraMap O T (f y y.1)`. Establish `hev : ∀ y z, ((h y : T) : X → O) z = f y z - f y y.1`. Introduce `y z`. Simplify using `[h]`.

Use `⟨∏ y, h y, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[coe_prod' T]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun y _ => by rw [hev]; exact sub_ne_zero.mpr (hf y)`. Introduce `y hy`. Rewrite using `[coe_prod' T]`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ ⟨y, hy⟩) (by rw [hev]; exact sub_self _)`.
-/
theorem exists_bump (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (x : X) :
    ∃ g : T, (g : X → O) x ≠ 0 ∧ ∀ y, y ≠ x → (g : X → O) y = 0 := by
  classical
  choose f hfT hf using fun y : {y : X // y ≠ x} => hsep x y.1 (Ne.symm y.2)
  let h : {y : X // y ≠ x} → T := fun y => ⟨f y, hfT y⟩ - algebraMap O T (f y y.1)
  have hev : ∀ y z, ((h y : T) : X → O) z = f y z - f y y.1 := by
    intro y z
    simp [h]
  refine ⟨∏ y, h y, ?_, ?_⟩
  · rw [coe_prod' T]
    exact Finset.prod_ne_zero_iff.mpr fun y _ => by rw [hev]; exact sub_ne_zero.mpr (hf y)
  · intro y hy
    rw [coe_prod' T]
    exact Finset.prod_eq_zero (Finset.mem_univ ⟨y, hy⟩) (by rw [hev]; exact sub_self _)

/- English proof (translation)
Use `choose g hgx hgy using fun x => exists_bump T hsep x`. Use `⟨∏ x, (g x : X → O) x, Finset.prod_ne_zero_iff.mpr fun x _ => hgx x, fun S => ?_⟩` and prove the remaining obligations. Use `⟨∑ x ∈ S, g x * algebraMap O T (∏ x' ∈ Finset.univ.erase x, (g x' : X → O) x'), fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[coe_sum' T]`. Establish `hterm : ∀ x, ((g x * algebraMap O T (∏ x' ∈ Finset.univ.erase x, (g x' : X → O) x') : T) : X → O) y = if y = x then ∏ x, (g x : X → O) x else 0`.

Introduce `x`. Establish `hc : ((g x * algebraMap O T (∏ x' ∈ Finset.univ.erase x, (g x' : X → O) x') : T) : X → O) y = (g x : X → O) y * ∏ x' ∈ Finset.univ.erase x, (g x' : X → O) x'`. Simplify using the standard rewrite rules. Rewrite using `[hc]`. Use `split_ifs with hxy`.

Substitute `hxy` using the available equality. Conclude with `Finset.mul_prod_erase Finset.univ (fun x' => (g x' : X → O) x') (Finset.mem_univ _)`. Rewrite using `[hgy x y hxy, zero_mul]`. Simplify using `only [hterm]`. Rewrite using `[Finset.sum_ite_eq]`.
-/
theorem exists_ind (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) :
    ∃ C : O, C ≠ 0 ∧ ∀ S : Finset X, ∃ e : T, ∀ y, (e : X → O) y = if y ∈ S then C else 0 := by
  classical
  choose g hgx hgy using fun x => exists_bump T hsep x
  refine ⟨∏ x, (g x : X → O) x, Finset.prod_ne_zero_iff.mpr fun x _ => hgx x, fun S => ?_⟩
  refine ⟨∑ x ∈ S, g x * algebraMap O T (∏ x' ∈ Finset.univ.erase x, (g x' : X → O) x'), fun y => ?_⟩
  rw [coe_sum' T]
  have hterm : ∀ x, ((g x * algebraMap O T (∏ x' ∈ Finset.univ.erase x, (g x' : X → O) x') : T) :
      X → O) y = if y = x then ∏ x, (g x : X → O) x else 0 := by
    intro x
    have hc : ((g x * algebraMap O T (∏ x' ∈ Finset.univ.erase x, (g x' : X → O) x') : T) :
        X → O) y = (g x : X → O) y * ∏ x' ∈ Finset.univ.erase x, (g x' : X → O) x' := by
      simp
    rw [hc]
    split_ifs with hxy
    · subst hxy
      exact Finset.mul_prod_erase Finset.univ (fun x' => (g x' : X → O) x') (Finset.mem_univ _)
    · rw [hgy x y hxy, zero_mul]
  simp only [hterm]
  rw [Finset.sum_ite_eq]

end Bump

section Main

open Formalism.NG Formalism.NG.QuotientPowerLengths

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type} [Fintype X]
  {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]
  (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M)

def actK : T →ₐ[O] Module.End (FractionRing O) (TensorProduct O (FractionRing O) M) :=
  (Module.End.baseChangeHom O (FractionRing O) M).comp act

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem actK_apply (f : T) : actK T act f = (act f).baseChange (FractionRing O) := rfl

/- English proof (translation)
Unfold `Formalism.BasicNotions.heckeEig Formalism.NG.Vx`. Use `iInf_congr fun f => ?_` and prove the remaining obligations. Use extensionality with `v`. Rewrite using `[Module.End.mem_eigenspace_iff, LinearMap.mem_ker]`. Simplify using `[actK_apply, sub_eq_zero]`.
-/
theorem heckeEig_eq (x : X) :
    heckeEig T act x = Vx T (actK T act).toRingHom x := by
  unfold Formalism.BasicNotions.heckeEig Formalism.NG.Vx
  refine iInf_congr fun f => ?_
  ext v
  rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker]
  simp [actK_apply, sub_eq_zero]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `y`. Use `show (f : X → O) y * (e : X → O) y = (f : X → O) x * (e : X → O) y`. Rewrite using `[he y]`. Use `split_ifs with h`.

Rewrite using `[Finset.mem_singleton.mp h]`. Simplify using the standard rewrite rules.
-/
theorem mul_ind [DecidableEq X] {C : O} {x : X} {e : T}
    (he : ∀ y, (e : X → O) y = if y ∈ ({x} : Finset X) then C else 0) (f : T) :
    f * e = ((f : X → O) x) • e := by
  apply Subtype.ext
  funext y
  show (f : X → O) y * (e : X → O) y = (f : X → O) x * (e : X → O) y
  rw [he y]
  split_ifs with h
  · rw [Finset.mem_singleton.mp h]
  · simp

/- English proof (translation)
Take `⟨C, hC, hind⟩` from `exists_ind T hsep`. Use `choose e he using fun x : X => hind {x}`. Establish `hsum : ∑ x, e x = algebraMap O T C`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `y`.

Rewrite using `[coe_sum' T]`. Simplify using `[he]`. Establish `hmemV : ∀ x (v : TensorProduct O (FractionRing O) M), actK T act (e x) v ∈ Vx T (actK T act).toRingHom x`. Introduce `x v`. Unfold `Formalism.NG.Vx`.

Use `Submodule.mem_iInf _ |>.mpr fun f => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker]`. Establish `hm` using `mul_ind T (he x) f`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, hm, map_smul, LinearMap.smul_apply, algebraMap_smul, sub_self]`.

Rewrite using `[eq_top_iff]`. Introduce `v _`. Establish `hCK : algebraMap O (FractionRing O) C ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hC`. Establish `hv : algebraMap O (FractionRing O) C • v = ∑ x, actK T act (e x) v`. Rewrite using `[← LinearMap.sum_apply, ← map_sum, hsum, AlgHom.commutes, Module.algebraMap_end_apply, algebraMap_smul]`.

Establish `h1 : algebraMap O (FractionRing O) C • v ∈ ⨆ x, Vx T (actK T act).toRingHom x`. Rewrite using `[hv]`. Conclude with `Submodule.sum_mem _ fun x _ => Submodule.mem_iSup_of_mem x (hmemV x v)`. Establish `h2` using `Submodule.smul_mem _ (algebraMap O (FractionRing O) C)⁻¹ h1`. Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ hCK, one_smul]`. Then use the resulting hypothesis.
-/
theorem eigSpan (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) :
    (⨆ x, Vx T (actK T act).toRingHom x) = ⊤ := by
  classical
  obtain ⟨C, hC, hind⟩ := exists_ind T hsep
  choose e he using fun x : X => hind {x}
  have hsum : ∑ x, e x = algebraMap O T C := by
    apply Subtype.ext
    funext y
    rw [coe_sum' T]
    simp [he]
  have hmemV : ∀ x (v : TensorProduct O (FractionRing O) M),
      actK T act (e x) v ∈ Vx T (actK T act).toRingHom x := by
    intro x v
    unfold Formalism.NG.Vx
    refine Submodule.mem_iInf _ |>.mpr fun f => ?_
    rw [LinearMap.mem_ker]
    have hm := mul_ind T (he x) f
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← Module.End.mul_apply, ← map_mul, hm, map_smul, LinearMap.smul_apply, algebraMap_smul,
      sub_self]
  rw [eq_top_iff]
  intro v _
  have hCK : algebraMap O (FractionRing O) C ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hC
  have hv : algebraMap O (FractionRing O) C • v = ∑ x, actK T act (e x) v := by
    rw [← LinearMap.sum_apply, ← map_sum, hsum, AlgHom.commutes, Module.algebraMap_end_apply,
      algebraMap_smul]
  have h1 : algebraMap O (FractionRing O) C • v ∈ ⨆ x, Vx T (actK T act).toRingHom x := by
    rw [hv]
    exact Submodule.sum_mem _ fun x _ => Submodule.mem_iSup_of_mem x (hmemV x v)
  have h2 := Submodule.smul_mem _ (algebraMap O (FractionRing O) C)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hCK, one_smul] at h2

/- English proof (translation)
Take `⟨C, hC, hind⟩` from `exists_ind T hsep`. Use `choose e he using fun x : X => hind {x}`. Establish `hsumAll : ∑ x, e x = algebraMap O T C`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `y`.

Rewrite using `[coe_sum' T]`. Simplify using `[he]`. Establish `hfun : ∀ (s : Finset X) y, ((∑ x ∈ s, e x : T) : X → O) y = if y ∈ s then C else 0`. Introduce `s y`. Rewrite using `[coe_sum' T]`.

Simplify using `[he]`. Establish `hmemV : ∀ x (v : TensorProduct O (FractionRing O) M), actK T act (e x) v ∈ Vx T (actK T act).toRingHom x`. Introduce `x v`. Unfold `Formalism.NG.Vx`. Use `Submodule.mem_iInf _ |>.mpr fun f => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.mem_ker]`. Establish `hm` using `mul_ind T (he x) f`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, hm, map_smul, LinearMap.smul_apply, algebraMap_smul, sub_self]`. Establish `hvx : ∀ x (f : T) (v : TensorProduct O (FractionRing O) M), v ∈ Vx T (actK T act).toRingHom x → actK T act f v = algebraMap O (FractionRing O) ((f : X → O) x) • v`.

Introduce `x f v hv`. Unfold `Formalism.NG.Vx at hv`. Establish `h` using `(Submodule.mem_iInf _).mp hv f`. Rewrite `h` using `[LinearMap.mem_ker]`. Simplify `h` using `[sub_eq_zero]`.

Establish `hcK : algebraMap O (FractionRing O) C ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hC`. Establish `hAle : VS T (actK T act).toRingHom (S : Set X) ≤ LinearMap.ker (actK T act (∑ x ∈ S, e x) - algebraMap O (FractionRing O) C • LinearMap.id)`. Unfold `Formalism.NG.VS`. Use `iSup₂_le fun x hx => ?_` and prove the remaining obligations. Introduce `v hv`.

Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, hvx x _ v hv, hfun S x, if_pos (Finset.mem_coe.mp hx)]`. Simplify using the standard rewrite rules. Establish `hBle : VS T (actK T act).toRingHom ((S : Set X)ᶜ) ≤ LinearMap.ker (actK T act (∑ x ∈ S, e x))`. Unfold `Formalism.NG.VS`. Use `iSup₂_le fun x hx => ?_` and prove the remaining obligations.

Introduce `v hv`. Establish `hx' : x ∉ S` using `fun h => hx (Finset.mem_coe.mpr h)`. Rewrite using `[LinearMap.mem_ker, hvx x _ v hv, hfun S x, if_neg hx']`. Simplify using the standard rewrite rules. Establish `hPA' : ∀ v, actK T act (∑ x ∈ S, e x) v ∈ VS T (actK T act).toRingHom (S : Set X)`.

Introduce `v`. Rewrite using `[map_sum, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun x hx => ?_` and prove the remaining obligations. Unfold `Formalism.NG.VS`. Conclude with `Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem (Finset.mem_coe.mpr hx) (hmemV x v))`.

Establish `hrest : ∀ v, actK T act (∑ x ∈ Finset.univ \ S, e x) v ∈ VS T (actK T act).toRingHom ((S : Set X)ᶜ)`. Introduce `v`. Rewrite using `[map_sum, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun x hx => ?_` and prove the remaining obligations. Establish `hx' : x ∈ ((S : Set X)ᶜ)` using `fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_coe.mp h)`.

Unfold `Formalism.NG.VS`. Conclude with `Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem hx' (hmemV x v))`. Establish `hcv : ∀ v, algebraMap O (FractionRing O) C • v = actK T act (∑ x ∈ Finset.univ \ S, e x) v + actK T act (∑ x ∈ S, e x) v`. Introduce `v`. Rewrite using `[← LinearMap.add_apply, ← map_add, Finset.sum_sdiff (Finset.subset_univ S), hsumAll, AlgHom.commutes, Module.algebraMap_end_apply, algebraMap_smul]`.

Establish `hPB' : ∀ v, v - (algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ S, e x) v ∈ VS T (actK T act).toRingHom ((S : Set X)ᶜ)`. Introduce `v`. Establish `h1 : v - (algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ S, e x) v = (algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ Finset.univ \ S, e x) v`. Rewrite using `[eq_inv_smul_iff₀ hcK, smul_sub, hcv v, smul_smul, mul_inv_cancel₀ hcK, one_smul, add_sub_cancel_right]`. Rewrite using `[h1]`.

Conclude with `Submodule.smul_mem _ _ (hrest v)`. Set `P : TensorProduct O (FractionRing O) M →ₗ[O] TensorProduct O (FractionRing O) M` to `((algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ S, e x)).restrictScalars O`. Use `quot_le L _ _ P ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `v hv`. Establish `h` using `hAle hv`.

Rewrite `h` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Use `show (algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ S, e x) v = v`. Rewrite using `[h, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, inv_mul_cancel₀ hcK, one_smul]`. Introduce `v hv`. Establish `h` using `LinearMap.mem_ker.mp (hBle hv)`.

Use `show (algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ S, e x) v = 0`. Rewrite using `[h, smul_zero]`. Introduce `v show (algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ S, e x) v ∈ VS T (actK T act).toRingHom (S : Set X)`. Conclude with `Submodule.smul_mem _ _ (hPA' v)`. Introduce `v`.

Conclude with `hPB' v`.
-/
theorem len_le (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y)
    (L : Submodule O (TensorProduct O (FractionRing O) M)) (S : Finset X) :
    Module.length O
      (↥((L ⊔ (VS T (actK T act).toRingHom (S : Set X)ᶜ).restrictScalars O) ⊓
          (VS T (actK T act).toRingHom (S : Set X)).restrictScalars O) ⧸
        (L ⊓ (VS T (actK T act).toRingHom (S : Set X)).restrictScalars O).comap
          ((L ⊔ (VS T (actK T act).toRingHom (S : Set X)ᶜ).restrictScalars O) ⊓
            (VS T (actK T act).toRingHom (S : Set X)).restrictScalars O).subtype) ≤
      Module.length O (CongMod T (actK T act).toRingHom L (S : Set X)) := by
  classical
  obtain ⟨C, hC, hind⟩ := exists_ind T hsep
  choose e he using fun x : X => hind {x}
  have hsumAll : ∑ x, e x = algebraMap O T C := by
    apply Subtype.ext
    funext y
    rw [coe_sum' T]
    simp [he]
  have hfun : ∀ (s : Finset X) y, ((∑ x ∈ s, e x : T) : X → O) y = if y ∈ s then C else 0 := by
    intro s y
    rw [coe_sum' T]
    simp [he]
  have hmemV : ∀ x (v : TensorProduct O (FractionRing O) M),
      actK T act (e x) v ∈ Vx T (actK T act).toRingHom x := by
    intro x v
    unfold Formalism.NG.Vx
    refine Submodule.mem_iInf _ |>.mpr fun f => ?_
    rw [LinearMap.mem_ker]
    have hm := mul_ind T (he x) f
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← Module.End.mul_apply, ← map_mul, hm, map_smul, LinearMap.smul_apply, algebraMap_smul,
      sub_self]
  have hvx : ∀ x (f : T) (v : TensorProduct O (FractionRing O) M),
      v ∈ Vx T (actK T act).toRingHom x →
        actK T act f v = algebraMap O (FractionRing O) ((f : X → O) x) • v := by
    intro x f v hv
    unfold Formalism.NG.Vx at hv
    have h := (Submodule.mem_iInf _).mp hv f
    rw [LinearMap.mem_ker] at h
    simpa [sub_eq_zero] using h
  have hcK : algebraMap O (FractionRing O) C ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hC
  have hAle : VS T (actK T act).toRingHom (S : Set X) ≤
      LinearMap.ker (actK T act (∑ x ∈ S, e x) - algebraMap O (FractionRing O) C • LinearMap.id) := by
    unfold Formalism.NG.VS
    refine iSup₂_le fun x hx => ?_
    intro v hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hvx x _ v hv, hfun S x,
      if_pos (Finset.mem_coe.mp hx)]
    simp
  have hBle : VS T (actK T act).toRingHom ((S : Set X)ᶜ) ≤
      LinearMap.ker (actK T act (∑ x ∈ S, e x)) := by
    unfold Formalism.NG.VS
    refine iSup₂_le fun x hx => ?_
    intro v hv
    have hx' : x ∉ S := fun h => hx (Finset.mem_coe.mpr h)
    rw [LinearMap.mem_ker, hvx x _ v hv, hfun S x, if_neg hx']
    simp
  have hPA' : ∀ v, actK T act (∑ x ∈ S, e x) v ∈ VS T (actK T act).toRingHom (S : Set X) := by
    intro v
    rw [map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun x hx => ?_
    unfold Formalism.NG.VS
    exact Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem (Finset.mem_coe.mpr hx) (hmemV x v))
  have hrest : ∀ v, actK T act (∑ x ∈ Finset.univ \ S, e x) v ∈
      VS T (actK T act).toRingHom ((S : Set X)ᶜ) := by
    intro v
    rw [map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun x hx => ?_
    have hx' : x ∈ ((S : Set X)ᶜ) := fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_coe.mp h)
    unfold Formalism.NG.VS
    exact Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem hx' (hmemV x v))
  have hcv : ∀ v, algebraMap O (FractionRing O) C • v =
      actK T act (∑ x ∈ Finset.univ \ S, e x) v + actK T act (∑ x ∈ S, e x) v := by
    intro v
    rw [← LinearMap.add_apply, ← map_add, Finset.sum_sdiff (Finset.subset_univ S), hsumAll,
      AlgHom.commutes, Module.algebraMap_end_apply, algebraMap_smul]
  have hPB' : ∀ v, v - (algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ S, e x) v ∈
      VS T (actK T act).toRingHom ((S : Set X)ᶜ) := by
    intro v
    have h1 : v - (algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ S, e x) v =
        (algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ Finset.univ \ S, e x) v := by
      rw [eq_inv_smul_iff₀ hcK, smul_sub, hcv v, smul_smul, mul_inv_cancel₀ hcK, one_smul,
        add_sub_cancel_right]
    rw [h1]
    exact Submodule.smul_mem _ _ (hrest v)
  let P : TensorProduct O (FractionRing O) M →ₗ[O] TensorProduct O (FractionRing O) M :=
    ((algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ S, e x)).restrictScalars O
  refine quot_le L _ _ P ?_ ?_ ?_ ?_
  · intro v hv
    have h := hAle hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
    show (algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ S, e x) v = v
    rw [h, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, inv_mul_cancel₀ hcK, one_smul]
  · intro v hv
    have h := LinearMap.mem_ker.mp (hBle hv)
    show (algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ S, e x) v = 0
    rw [h, smul_zero]
  · intro v
    show (algebraMap O (FractionRing O) C)⁻¹ • actK T act (∑ x ∈ S, e x) v ∈
      VS T (actK T act).toRingHom (S : Set X)
    exact Submodule.smul_mem _ _ (hPA' v)
  · intro v
    exact hPB' v

/- English proof (translation)
Simplify using `only [Formalism.BasicNotions.ccIdeal, Formalism.NG.ccIdeal, Formalism.NG.resOff, RingHom.mem_ker]`. Rewrite using `[funext_iff, funext_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h y`. Conclude with `h ⟨y.1, y.2⟩`.

Introduce `h y`. Conclude with `h ⟨y.1, y.2⟩`.
-/
theorem mem_ccIdeal_iff (Z : Finset X) (f : T) :
    f ∈ Formalism.BasicNotions.ccIdeal T Z ↔ f ∈ Formalism.NG.ccIdeal T (Z : Set X) := by
  simp only [Formalism.BasicNotions.ccIdeal, Formalism.NG.ccIdeal, Formalism.NG.resOff, RingHom.mem_ker]
  rw [funext_iff, funext_iff]
  constructor
  · intro h y
    exact h ⟨y.1, y.2⟩
  · intro h y
    exact h ⟨y.1, y.2⟩

/- English proof (translation)
Take `⟨c, hc, hval⟩` from `vcc_attain (T := T) (Z : Set X) π`. Establish `h : ccAt T Z π = Ideal.span {(c : X → O) π}`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[ccAt, Ideal.map_le_iff_le_comap]`. Introduce `f hf`.

Rewrite using `[Ideal.mem_comap, Ideal.mem_span_singleton]`. Use `show (c : X → O) π ∣ (f : X → O) π`. Rewrite using `[← addVal_le_iff_dvd, hval]`. Conclude with `iInf₂_le f ((mem_ccIdeal_iff T Z f).mp hf)`. Rewrite using `[Ideal.span_singleton_le_iff_mem]`.

Conclude with `Ideal.mem_map_of_mem _ ((mem_ccIdeal_iff T Z c).mpr hc)`. Rewrite using `[h, IdempotentNormalFormsLenFacts.length_quot_span, hval]`.
-/
theorem length_ccAt (Z : Finset X) (π : X) :
    Module.length O (O ⧸ ccAt T Z π) = vcc T (Z : Set X) π := by
  obtain ⟨c, hc, hval⟩ := vcc_attain (T := T) (Z : Set X) π
  have h : ccAt T Z π = Ideal.span {(c : X → O) π} := by
    apply le_antisymm
    · rw [ccAt, Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      show (c : X → O) π ∣ (f : X → O) π
      rw [← addVal_le_iff_dvd, hval]
      exact iInf₂_le f ((mem_ccIdeal_iff T Z f).mp hf)
    · rw [Ideal.span_singleton_le_iff_mem]
      exact Ideal.mem_map_of_mem _ ((mem_ccIdeal_iff T Z c).mpr hc)
  rw [h, IdempotentNormalFormsLenFacts.length_quot_span, hval]

/- English proof (translation)
Take `⟨C, hC, hind⟩` from `exists_ind T hsep`. Take `⟨e, he⟩` from `hind {π}`. Establish `heI : e ∈ Formalism.NG.ccIdeal T (Z : Set X)`. Simplify using `only [Formalism.NG.ccIdeal, RingHom.mem_ker]`. Use function extensionality and compare the values at `y`.

Establish `hy : y.1 ≠ π` using `fun h => y.2 (by rw [Finset.mem_coe, h]; exact hπ)`. Use `show (e : X → O) y.1 = 0`. Rewrite using `[he, if_neg (by simpa using hy)]`. Establish `hle : vcc T (Z : Set X) π ≤ IsDiscreteValuationRing.addVal O ((e : X → O) π)`. Unfold `Formalism.NG.vcc`.

Conclude with `iInf₂_le e heI`. Introduce `htop`. Rewrite `hle` using `[htop, top_le_iff, he, if_pos (Finset.mem_singleton_self π)]`. Conclude with `hC ((IsDiscreteValuationRing.addVal_eq_top_iff).mp hle)`.
-/
theorem vcc_ne_top (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (Z : Finset X) (π : X)
    (hπ : π ∈ Z) : vcc T (Z : Set X) π ≠ ⊤ := by
  classical
  obtain ⟨C, hC, hind⟩ := exists_ind T hsep
  obtain ⟨e, he⟩ := hind {π}
  have heI : e ∈ Formalism.NG.ccIdeal T (Z : Set X) := by
    simp only [Formalism.NG.ccIdeal, RingHom.mem_ker]
    funext y
    have hy : y.1 ≠ π := fun h => y.2 (by rw [Finset.mem_coe, h]; exact hπ)
    show (e : X → O) y.1 = 0
    rw [he, if_neg (by simpa using hy)]
  have hle : vcc T (Z : Set X) π ≤ IsDiscreteValuationRing.addVal O ((e : X → O) π) := by
    unfold Formalism.NG.vcc
    exact iInf₂_le e heI
  intro htop
  rw [htop, top_le_iff, he, if_pos (Finset.mem_singleton_self π)] at hle
  exact hC ((IsDiscreteValuationRing.addVal_eq_top_iff).mp hle)

/- English proof (translation)
Establish `hlp : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.mp (Fact.out)`. Take `⟨m, hm⟩ : (l : ℤ) ^ padicValInt l A ∣ A` from `(padicValInt_dvd_iff _ A).mpr (Or.inr le_rfl)`. Establish `hnd : ¬ (l : ℤ) ∣ m`. Introduce and unpack `⟨m', hm'⟩`. Establish `h2 : (l : ℤ) ^ (padicValInt l A + 1) ∣ A` using `Dvd.intro m' (by rw [pow_succ, mul_assoc, ← hm']; exact hm.symm)`.

Break down `(padicValInt_dvd_iff (padicValInt l A + 1) A).mp h2 with h | h` into its components or cases. Conclude with `hA h`. Use linear arithmetic over natural numbers and integers. Establish `hcop : IsCoprime (l : ℤ) m` using `(Irreducible.coprime_iff_not_dvd hlp.irreducible).mpr hnd`. Take `⟨u, v, huv⟩` from `hcop.map (Int.castRingHom O)`.

Establish `hmu : IsUnit (m : O)`. Break down `IsLocalRing.isUnit_or_isUnit_of_add_one huv with h | h` into its components or cases. Conclude with `absurd (isUnit_of_mul_isUnit_right h) (by simpa using hl)`. Simplify using `using isUnit_of_mul_isUnit_right h`. Take `⟨w, hw⟩` from `hmu`.

Use `conv_lhs => rw [hm]`. Use `push_cast`. Rewrite using `[IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, ← hw, IsDiscreteValuationRing.addVal_eq_zero_of_unit, add_zero, nsmul_eq_mul]`.
-/
theorem addVal_int (l : ℕ) [Fact l.Prime] (hl : ¬ IsUnit (l : O)) (A : ℤ) (hA : A ≠ 0) :
    addVal O (A : O) = (padicValInt l A : ℕ∞) * addVal O (l : O) := by
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out)
  obtain ⟨m, hm⟩ : (l : ℤ) ^ padicValInt l A ∣ A := (padicValInt_dvd_iff _ A).mpr (Or.inr le_rfl)
  have hnd : ¬ (l : ℤ) ∣ m := by
    rintro ⟨m', hm'⟩
    have h2 : (l : ℤ) ^ (padicValInt l A + 1) ∣ A :=
      Dvd.intro m' (by rw [pow_succ, mul_assoc, ← hm']; exact hm.symm)
    rcases (padicValInt_dvd_iff (padicValInt l A + 1) A).mp h2 with h | h
    · exact hA h
    · omega
  have hcop : IsCoprime (l : ℤ) m := (Irreducible.coprime_iff_not_dvd hlp.irreducible).mpr hnd
  obtain ⟨u, v, huv⟩ := hcop.map (Int.castRingHom O)
  have hmu : IsUnit (m : O) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one huv with h | h
    · exact absurd (isUnit_of_mul_isUnit_right h) (by simpa using hl)
    · simpa using isUnit_of_mul_isUnit_right h
  obtain ⟨w, hw⟩ := hmu
  conv_lhs => rw [hm]
  push_cast
  rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, ← hw,
    IsDiscreteValuationRing.addVal_eq_zero_of_unit, add_zero, nsmul_eq_mul]

def latIn (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] :
    Submodule O (TensorProduct O (FractionRing O) M) :=
  LinearMap.range (TensorProduct.mk O (FractionRing O) M 1)

/- English proof (translation)
Introduce `v hv`. Take `⟨m, rfl⟩` from `LinearMap.mem_range.mp hv`. Conclude with `LinearMap.mem_range.mpr ⟨β m, by simp [LinearMap.baseChange_tmul]⟩`.
-/
theorem baseChange_latIn (β : Module.End O M) :
    ∀ v ∈ latIn O M, β.baseChange (FractionRing O) v ∈ latIn O M := by
  intro v hv
  obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hv
  exact LinearMap.mem_range.mpr ⟨β m, by simp [LinearMap.baseChange_tmul]⟩

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce and unpack `v -`. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => exact zero_mem _`. Consider the case `tmul a m`.

Establish `ht : a ⊗ₜ[O] m = a • ((1 : FractionRing O) ⊗ₜ[O] m)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[ht]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (LinearMap.mem_range.mpr ⟨m, rfl⟩ : (1 : FractionRing O) ⊗ₜ[O] m ∈ latIn O M))`. Consider the case `add x y hx hy => exact add_mem hx hy`.
-/
theorem span_latIn : Submodule.span (FractionRing O) (latIn O M : Set (TensorProduct O (FractionRing O) M)) = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  induction v using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul a m =>
    have ht : a ⊗ₜ[O] m = a • ((1 : FractionRing O) ⊗ₜ[O] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      (LinearMap.mem_range.mpr ⟨m, rfl⟩ : (1 : FractionRing O) ⊗ₜ[O] m ∈ latIn O M))
  | add x y hx hy => exact add_mem hx hy

/- English proof (translation)
Unfold `latIn`. Rewrite using `[LinearMap.range_eq_map]`. Conclude with `(Module.Finite.fg_top).map _`.
-/
theorem fg_latIn : (latIn O M).FG := by
  unfold latIn
  rw [LinearMap.range_eq_map]
  exact (Module.Finite.fg_top).map _

/- English proof (translation)
Distinguish the cases in `he : (Module.length O (O ⧸ Ideal.span {(l : O)})).toNat = 0`. Simplify using `only [lenUnit, he, Nat.cast_zero, div_zero, zero_add]`. Conclude with `Finset.sum_nonneg fun π _ => by positivity`. Establish `heO : Module.length O (O ⧸ Ideal.span {(l : O)}) = addVal O (l : O)` using `IdempotentNormalFormsLenFacts.length_quot_span _`. Choose the witnesses or unpack the hypotheses as in `⟨e, hee⟩ : ∃ e : ℕ, addVal O (l : O) = (e : ℕ∞) := by`.

Rewrite `he` using `[heO]`. Conclude with `⟨(addVal O (l : O)).toNat, (ENat.natCast_toNat (fun h => he (by rw [h]; rfl))).symm⟩`. Establish `he0 : e ≠ 0`. Rewrite `he` using `[heO, hee]`. Simplify using `using he`.

Establish `hlu : ¬ IsUnit (l : O)`. Introduce `h`. Rewrite `hee` using `[addVal_eq_zero_iff.mpr h]`. Conclude with `he0 (by exact_mod_cast hee.symm)`. Establish `hcore` using `etaBound O X T hsep (TensorProduct O (FractionRing O) M) (actK T act).toRingHom (eigSpan T act hsep) (latIn O M) fg_latIn span_latIn (fun f v hv => baseChange_latIn (act f) v hv) Z Z' hZ' (α.baseChange (FractionRing O)) A (baseChange_latIn α) (fun f => by show Module.End.baseChan …`.

Rewrite using `[← map_mul, ← map_mul, hcomm f])`. Use the proof step `(fun x hx v hv => h1 x hx v (by rw [heckeEig_eq]; exact hv))`. Use the proof step `(fun x hx hx' v hv => h0 x hx hx' v (by rw [heckeEig_eq]; exact hv))`. Use the proof step `(fun x => vcc T (Z : Set X) x) (fun x _ => le_rfl)`. Establish `hlen` using `(len_le T act hsep (latIn O M) Z').trans hcore`.

Establish `hE : heckeEig T act = Vx T (actK T act).toRingHom` using `funext (heckeEig_eq T act)`. Simplify using `only [heckeMult, lenUnit, length_ccAt, heO, hee, ENat.toNat_natCast]`. Rewrite using `[hE]`. Rewrite `hlen` using `[addVal_int l hlu A hA, hee]`. Establish `hfin : ∀ π ∈ Z', vcc T (Z : Set X) π = ((vcc T (Z : Set X) π).toNat : ℕ∞)` using `fun π hπ => (ENat.natCast_toNat (vcc_ne_top T hsep Z π (hZ' hπ))).symm`.

Establish `hsum : ∑ x ∈ Z', (Module.finrank (FractionRing O) (Vx T (actK T act).toRingHom x) : ℕ∞) * (vcc T (Z : Set X) x + (padicValInt l A : ℕ∞) * (e : ℕ∞)) = ((∑ x ∈ Z', Module.finrank (FractionRing O) (Vx T (actK T act).toRingHom x) * ((vcc T (Z : Set X) x).toNat + padicValInt l A * e) …`. Use `push_cast`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[← hfin x hx]`. Rewrite `hlen` using `[hsum]`.

Establish `hnat` using `ENat.toNat_le_of_le_natCast hlen`. Establish `heq : (0 : ℚ) < e` using `by exact_mod_cast Nat.pos_of_ne_zero he0`. Rewrite using `[div_le_iff₀ heq, Finset.sum_mul]`. Use `(Nat.cast_le (α := ℚ).mpr hnat).trans (le_of_eq ?_)` and prove the remaining obligations. Use `push_cast`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.
-/
theorem hecke_length_bound [IsLocalRing T] (l : ℕ) [Fact l.Prime]
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (Z Z' : Finset X) (hZ' : Z' ⊆ Z)
    (α : Module.End O M) (A : ℤ) (hA : A ≠ 0) (hcomm : ∀ f : T, α * act f = act f * α)
    (h1 : ∀ x ∈ Z', ∀ u ∈ heckeEig T act x,
      α.baseChange (FractionRing O) u = (A : FractionRing O) • u)
    (h0 : ∀ x ∈ Z, x ∉ Z' → ∀ u ∈ heckeEig T act x, α.baseChange (FractionRing O) u = 0) :
    lenUnit (O := O) l
        (↥((latIn O M ⊔ (⨆ x ∈ (Z' : Set X)ᶜ, heckeEig T act x).restrictScalars O) ⊓
            (⨆ x ∈ (Z' : Set X), heckeEig T act x).restrictScalars O) ⧸
          (latIn O M ⊓ (⨆ x ∈ (Z' : Set X), heckeEig T act x).restrictScalars O).comap
            ((latIn O M ⊔ (⨆ x ∈ (Z' : Set X)ᶜ, heckeEig T act x).restrictScalars O) ⊓
              (⨆ x ∈ (Z' : Set X), heckeEig T act x).restrictScalars O).subtype) ≤
      ∑ π ∈ Z', (heckeMult T act π : ℚ) *
        (lenUnit (O := O) l (O ⧸ ccAt T Z π) + padicValInt l A) := by
  by_cases he : (Module.length O (O ⧸ Ideal.span {(l : O)})).toNat = 0
  · simp only [lenUnit, he, Nat.cast_zero, div_zero, zero_add]
    exact Finset.sum_nonneg fun π _ => by positivity
  have heO : Module.length O (O ⧸ Ideal.span {(l : O)}) = addVal O (l : O) :=
    IdempotentNormalFormsLenFacts.length_quot_span _
  obtain ⟨e, hee⟩ : ∃ e : ℕ, addVal O (l : O) = (e : ℕ∞) := by
    rw [heO] at he
    exact ⟨(addVal O (l : O)).toNat, (ENat.natCast_toNat (fun h => he (by rw [h]; rfl))).symm⟩
  have he0 : e ≠ 0 := by
    rw [heO, hee] at he
    simpa using he
  have hlu : ¬ IsUnit (l : O) := by
    intro h
    rw [addVal_eq_zero_iff.mpr h] at hee
    exact he0 (by exact_mod_cast hee.symm)
  have hcore := etaBound O X T hsep (TensorProduct O (FractionRing O) M) (actK T act).toRingHom
    (eigSpan T act hsep) (latIn O M) fg_latIn span_latIn
    (fun f v hv => baseChange_latIn (act f) v hv) Z Z' hZ' (α.baseChange (FractionRing O)) A
    (baseChange_latIn α)
    (fun f => by
      show Module.End.baseChangeHom O (FractionRing O) M α *
          Module.End.baseChangeHom O (FractionRing O) M (act f) =
        Module.End.baseChangeHom O (FractionRing O) M (act f) *
          Module.End.baseChangeHom O (FractionRing O) M α
      rw [← map_mul, ← map_mul, hcomm f])
    (fun x hx v hv => h1 x hx v (by rw [heckeEig_eq]; exact hv))
    (fun x hx hx' v hv => h0 x hx hx' v (by rw [heckeEig_eq]; exact hv))
    (fun x => vcc T (Z : Set X) x) (fun x _ => le_rfl)
  have hlen := (len_le T act hsep (latIn O M) Z').trans hcore
  have hE : heckeEig T act = Vx T (actK T act).toRingHom := funext (heckeEig_eq T act)
  simp only [heckeMult, lenUnit, length_ccAt, heO, hee, ENat.toNat_natCast]
  rw [hE]
  rw [addVal_int l hlu A hA, hee] at hlen
  have hfin : ∀ π ∈ Z', vcc T (Z : Set X) π = ((vcc T (Z : Set X) π).toNat : ℕ∞) :=
    fun π hπ => (ENat.natCast_toNat (vcc_ne_top T hsep Z π (hZ' hπ))).symm
  have hsum : ∑ x ∈ Z', (Module.finrank (FractionRing O) (Vx T (actK T act).toRingHom x) : ℕ∞) *
        (vcc T (Z : Set X) x + (padicValInt l A : ℕ∞) * (e : ℕ∞)) =
      ((∑ x ∈ Z', Module.finrank (FractionRing O) (Vx T (actK T act).toRingHom x) *
        ((vcc T (Z : Set X) x).toNat + padicValInt l A * e) : ℕ) : ℕ∞) := by
    push_cast
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← hfin x hx]
  rw [hsum] at hlen
  have hnat := ENat.toNat_le_of_le_natCast hlen
  have heq : (0 : ℚ) < e := by exact_mod_cast Nat.pos_of_ne_zero he0
  rw [div_le_iff₀ heq, Finset.sum_mul]
  refine (Nat.cast_le (α := ℚ).mpr hnat).trans (le_of_eq ?_)
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  field_simp

end Main

/- English proof (translation)
Use `N.T_local i` as an intermediate fact. Conclude with `hecke_length_bound (N.T i) (N.act i) (N.l i) (N.T_sep i) (N.Z i) Z' hZ' α A hA hcomm h1 h0`.
-/
theorem hecke_length_bound_localised {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)
    (Z' : Finset (N.X i)) (hZ' : Z' ⊆ N.Z i) (α : Module.End (N.O i) (N.Mt i)) (A : ℤ) (hA : A ≠ 0)
    (hcomm : ∀ f : N.T i, α * N.act i f = N.act i f * α)
    (h1 : ∀ x ∈ Z', ∀ u ∈ heckeEig (N.T i) (N.act i) x,
      α.baseChange (Formalism.MainNotions.N.KK N i) u = (A : Formalism.MainNotions.N.KK N i) • u)
    (h0 : ∀ x ∈ N.Z i, x ∉ Z' → ∀ u ∈ heckeEig (N.T i) (N.act i) x,
      α.baseChange (Formalism.MainNotions.N.KK N i) u = 0) :
    lenUnit (O := N.O i) (N.l i)
        (↥(Formalism.MainNotions.N.MtUp N i Z') ⧸ (Formalism.MainNotions.N.MtLow N i Z').comap (Formalism.MainNotions.N.MtUp N i Z').subtype) ≤
      ∑ π ∈ Z', (N.mult i π : ℚ) * (N.vcc i π + padicValInt (N.l i) A) := by
  have := N.T_local i
  exact hecke_length_bound (N.T i) (N.act i) (N.l i) (N.T_sep i) (N.Z i) Z' hZ' α A hA hcomm h1 h0

/- English proof (translation)
Introduce `i`. Establish `h` using `eigSpan (N.T i) (N.act i) (N.T_sep i)`. Establish `hE : heckeEig (N.T i) (N.act i) = Formalism.NG.Vx (N.T i) (actK (N.T i) (N.act i)).toRingHom`. Use function extensionality and compare the values at `(heckeEig_eq (N.T i) (N.act i))`. Rewrite using `[hE]`.

Conclude with `h`.
-/
theorem EigSpan_holds {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) :
    N.EigSpan := by
  intro i
  have h := eigSpan (N.T i) (N.act i) (N.T_sep i)
  have hE : heckeEig (N.T i) (N.act i) = Formalism.NG.Vx (N.T i) (actK (N.T i) (N.act i)).toRingHom :=
    funext (heckeEig_eq (N.T i) (N.act i))
  rw [hE]
  exact h

/- English proof (translation)
Unfold `Formalism.BasicNotions.NData.etaLoc Formalism.BasicNotions.NData.MtUp Formalism.BasicNotions.NData.MtLow Formalism.MainNotions.N.MtUp Formalism.MainNotions.N.MtLow`. Rewrite using `[inf_comm (Submodule.restrictScalars (N.O i) (N.eigSum i ((N.Zgood i : Finset (N.X i)) : Set (N.X i))))]`. Both sides reduce to the same expression.
-/
theorem etaLoc_eq {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) :
    N.etaLoc i = lenUnit (O := N.O i) (N.l i)
      (↥(Formalism.MainNotions.N.MtUp N i (N.Zgood i)) ⧸
        (Formalism.MainNotions.N.MtLow N i (N.Zgood i)).comap (Formalism.MainNotions.N.MtUp N i (N.Zgood i)).subtype) := by
  unfold Formalism.BasicNotions.NData.etaLoc Formalism.BasicNotions.NData.MtUp Formalism.BasicNotions.NData.MtLow Formalism.MainNotions.N.MtUp Formalism.MainNotions.N.MtLow
  rw [inf_comm (Submodule.restrictScalars (N.O i)
    (N.eigSum i ((N.Zgood i : Finset (N.X i)) : Set (N.X i))))]
  rfl

section Unit

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)

/- English proof (translation)
Introduce `h`. Establish `h1 : ((N.l i : ℕ) : what₂.LL) ≠ 0`. Introduce `h0`. Establish `h2` using `congrArg what₂.embLL h0`. Rewrite `h2` using `[map_natCast, map_zero]`.

Conclude with `(N.lPrime i).out.ne_zero (by exact_mod_cast h2)`. Establish `h3 : N.embK i ((N.l i : ℕ) : what₂.LL) = 0`. Rewrite using `[map_natCast, ← map_natCast (algebraMap (N.O i) (FractionRing (N.O i))), h, map_zero]`. Conclude with `h1 ((map_eq_zero (N.embK i)).mp h3)`.
-/
theorem l_ne_zero : ((N.l i : ℕ) : N.O i) ≠ 0 := by
  intro h
  have h1 : ((N.l i : ℕ) : what₂.LL) ≠ 0 := by
    intro h0
    have h2 := congrArg what₂.embLL h0
    rw [map_natCast, map_zero] at h2
    exact (N.lPrime i).out.ne_zero (by exact_mod_cast h2)
  have h3 : N.embK i ((N.l i : ℕ) : what₂.LL) = 0 := by
    rw [map_natCast, ← map_natCast (algebraMap (N.O i) (FractionRing (N.O i))), h, map_zero]
  exact h1 ((map_eq_zero (N.embK i)).mp h3)

/- English proof (translation)
Introduce `hu`. Establish `hker : RingHom.ker (algebraMap ℤ_[N.l i] (N.O i)) ≤ IsLocalRing.maximalIdeal ℤ_[N.l i]` using `IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)`. Take `⟨Q, hQ, hQc⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := N.O i) (IsLocalRing.maximalIdeal ℤ_[N.l i]) hker`. Establish `hl : ((N.l i : ℕ) : ℤ_[N.l i]) ∈ IsLocalRing.maximalIdeal ℤ_[N.l i]`. Rewrite using `[PadicInt.maximalIdeal_eq_span_p]`.

Conclude with `Ideal.mem_span_singleton_self _`. Rewrite `hl` using `[← hQc, Ideal.mem_comap, map_natCast]`. Conclude with `hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hl hu)`.
-/
theorem l_not_unit : ¬ IsUnit ((N.l i : ℕ) : N.O i) := by
  intro hu
  have hker : RingHom.ker (algebraMap ℤ_[N.l i] (N.O i)) ≤ IsLocalRing.maximalIdeal ℤ_[N.l i] :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := N.O i)
    (IsLocalRing.maximalIdeal ℤ_[N.l i]) hker
  have hl : ((N.l i : ℕ) : ℤ_[N.l i]) ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  rw [← hQc, Ideal.mem_comap, map_natCast] at hl
  exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hl hu)

/- English proof (translation)
Establish `h0` using `l_ne_zero N i`. Establish `h1` using `l_not_unit N i`. Establish `htop : addVal (N.O i) ((N.l i : ℕ) : N.O i) ≠ ⊤` using `fun h => h0 ((IsDiscreteValuationRing.addVal_eq_top_iff).mp h)`. Use `⟨(addVal (N.O i) ((N.l i : ℕ) : N.O i)).toNat, ?_, (ENat.coe_toNat htop).symm⟩` and prove the remaining obligations. Introduce `h`.

Break down `ENat.toNat_eq_zero.mp h with h | h` into its components or cases. Conclude with `h1 ((IsDiscreteValuationRing.addVal_eq_zero_iff).mp h)`. Conclude with `htop h`.
-/
theorem exists_eO : ∃ e : ℕ, e ≠ 0 ∧ addVal (N.O i) ((N.l i : ℕ) : N.O i) = (e : ℕ∞) := by
  have h0 := l_ne_zero N i
  have h1 := l_not_unit N i
  have htop : addVal (N.O i) ((N.l i : ℕ) : N.O i) ≠ ⊤ := fun h =>
    h0 ((IsDiscreteValuationRing.addVal_eq_top_iff).mp h)
  refine ⟨(addVal (N.O i) ((N.l i : ℕ) : N.O i)).toNat, ?_, (ENat.coe_toNat htop).symm⟩
  intro h
  rcases ENat.toNat_eq_zero.mp h with h | h
  · exact h1 ((IsDiscreteValuationRing.addVal_eq_zero_iff).mp h)
  · exact htop h

/- English proof (translation)
Take `⟨e, he0, he⟩` from `exists_eO N i`. Unfold `lenUnit`. Rewrite using `[Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, ha, he]`. Establish `h : ((m : ℕ∞) * (e : ℕ∞)).toNat = m * e`. Rewrite using `[← Nat.cast_mul, ENat.toNat_natCast]`.

Rewrite using `[h, ENat.toNat_natCast]`. Establish `: (e : ℚ) ≠ 0` using `by exact_mod_cast he0`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem lenUnit_span {a : N.O i} {m : ℕ}
    (ha : addVal (N.O i) a = (m : ℕ∞) * addVal (N.O i) ((N.l i : ℕ) : N.O i)) :
    lenUnit (O := N.O i) (N.l i) (N.O i ⧸ Ideal.span {a}) = (m : ℚ) := by
  obtain ⟨e, he0, he⟩ := exists_eO N i
  unfold lenUnit
  rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, ha, he]
  have h : ((m : ℕ∞) * (e : ℕ∞)).toNat = m * e := by
    rw [← Nat.cast_mul, ENat.toNat_natCast]
  rw [h, ENat.toNat_natCast]
  have : (e : ℚ) ≠ 0 := by exact_mod_cast he0
  push_cast
  field_simp

end Unit

section Del

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Use `set y : ℤ_[l] := 1 + (l : ℤ_[l]) ^ s₀ * (u : ℤ_[l]) with hy`. Use `set m : ℕ := s₀ + padicValNat l k with hm`. Take `⟨z, hz⟩` from `Ideal.mem_span_singleton.mp (PadicInt.appr_spec (m + 1) y)`. Use `set x : ℤ := ((y.appr (m + 1) : ℕ) : ℤ) with hx`. Establish `hyx : y = (x : ℤ_[l]) + (l : ℤ_[l]) ^ (m + 1) * z`.

Establish `: (x : ℤ_[l]) = ((y.appr (m + 1) : ℕ) : ℤ_[l])` using `by rw [hx]; push_cast; rfl`. Rewrite using `[this, ← hz]`. Expand and normalize the polynomial expressions, which then agree. Establish `hms : m + 1 = s₀ + (padicValNat l k + 1)` using `by omega`. Establish `hx1 : ((x - 1 : ℤ) : ℤ_[l]) = (l : ℤ_[l]) ^ s₀ * ((u : ℤ_[l]) - (l : ℤ_[l]) ^ (padicValNat l k + 1) * z)`.

Establish `h : (x : ℤ_[l]) = y - (l : ℤ_[l]) ^ (m + 1) * z` using `by rw [hyx]; ring`. Use `push_cast`. Rewrite using `[h, hy, hms, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd1 : (l : ℤ) ^ s₀ ∣ x - 1`.

Rewrite using `[← PadicInt.pow_p_dvd_int_iff, hx1]`. Conclude with `Dvd.intro _ rfl`. Establish `hd2 : ¬ (l : ℤ) ^ (s₀ + 1) ∣ x - 1`. Rewrite using `[← PadicInt.pow_p_dvd_int_iff, hx1, pow_succ]`. Introduce `h`.

Establish `hp0 : (l : ℤ_[l]) ^ s₀ ≠ 0` using `pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)`. Establish `h3` using `(mul_dvd_mul_iff_left hp0).mp h`. Establish `h4 : (l : ℤ_[l]) ∣ (u : ℤ_[l])`. Establish `h5 : (l : ℤ_[l]) ∣ (l : ℤ_[l]) ^ (padicValNat l k + 1) * z` using `Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero _)) _`. Use `dvd_add h3 h5` as an intermediate fact.

Simplify using `using this`. Conclude with `PadicInt.prime_p.not_isUnit (isUnit_of_dvd_unit h4 u.isUnit)`. Establish `hcore` using `Formalism.NG.character_column_kernel_length_bound l s₀ h1 h2 x hd1 hd2 0 k hk`. Rewrite `hcore` using `[pow_zero, Nat.sub_zero]`. Establish `hne : x ^ k - 1 ≠ 0`.

Introduce `h0`. Rewrite `hcore` using `[h0, padicValInt.zero]`. Use linear arithmetic over natural numbers and integers. Establish `hA` using `addVal_int (O := O) l hlu (x ^ k - 1) hne`. Rewrite `hA` using `[hcore]`.

Take `⟨q, hq⟩ : (algebraMap ℤ_[l] O y - (x : O)) ∣ (algebraMap ℤ_[l] O y) ^ k - (x : O) ^ k` from `sub_dvd_pow_sub_pow _ _ _`. Establish `hyO : algebraMap ℤ_[l] O y - (x : O) = (l : O) ^ (m + 1) * algebraMap ℤ_[l] O z`. Rewrite using `[hyx, map_add, map_mul, map_pow, map_natCast, map_intCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsplit : (algebraMap ℤ_[l] O y) ^ k - 1 = ((x ^ k - 1 : ℤ) : O) + (l : O) ^ (m + 1) * (algebraMap ℤ_[l] O z * q)`.

Establish `: (algebraMap ℤ_[l] O y) ^ k = (x : O) ^ k + (l : O) ^ (m + 1) * algebraMap ℤ_[l] O z * q`. Rewrite using `[← hyO, ← hq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨e, he⟩ : ∃ e : ℕ, addVal O (l : O) = (e : ℕ∞)` from `⟨(addVal O (l : O)).toNat, (ENat.natCast_toNat (fun h => hl0 (addVal_eq_top_iff.mp h))).symm⟩`. Establish `he0 : 0 < e`. Break down `Nat.eq_zero_or_pos e with h | h` into its components or cases. Rewrite `he` using `[h]`.

Conclude with `absurd (addVal_eq_zero_iff.mp (by simpa using he)) hlu`. Conclude with `h`. Establish `hlt : addVal O ((x ^ k - 1 : ℤ) : O) < addVal O ((l : O) ^ (m + 1) * (algebraMap ℤ_[l] O z * q))`. Rewrite using `[hA, addVal_mul, addVal_pow, he]`. Establish `h6 : ((m : ℕ) : ℕ∞) * (e : ℕ∞) < (m + 1) • (e : ℕ∞)`.

Rewrite using `[nsmul_eq_mul]`. Establish `: m * e < (m + 1) * e` using `by nlinarith`. Conclude with `this` after adjusting the coercions. Conclude with `lt_of_lt_of_le h6 le_self_add`. Rewrite using `[hsplit, AddValuation.map_add_eq_of_lt_left _ hlt, hA]`.
-/
theorem addVal_pow_sub_one (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] (hl0 : (l : O) ≠ 0)
    (hlu : ¬ IsUnit (l : O)) (s₀ : ℕ) (h1 : 1 ≤ s₀) (h2 : l = 2 → 2 ≤ s₀) (u : ℤ_[l]ˣ) (k : ℕ)
    (hk : 0 < k) :
    addVal O ((algebraMap ℤ_[l] O (1 + (l : ℤ_[l]) ^ s₀ * (u : ℤ_[l]))) ^ k - 1) =
      ((s₀ + padicValNat l k : ℕ) : ℕ∞) * addVal O (l : O) := by
  set y : ℤ_[l] := 1 + (l : ℤ_[l]) ^ s₀ * (u : ℤ_[l]) with hy
  set m : ℕ := s₀ + padicValNat l k with hm
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec (m + 1) y)
  set x : ℤ := ((y.appr (m + 1) : ℕ) : ℤ) with hx
  have hyx : y = (x : ℤ_[l]) + (l : ℤ_[l]) ^ (m + 1) * z := by
    have : (x : ℤ_[l]) = ((y.appr (m + 1) : ℕ) : ℤ_[l]) := by rw [hx]; push_cast; rfl
    rw [this, ← hz]
    ring
  have hms : m + 1 = s₀ + (padicValNat l k + 1) := by omega
  have hx1 : ((x - 1 : ℤ) : ℤ_[l]) =
      (l : ℤ_[l]) ^ s₀ * ((u : ℤ_[l]) - (l : ℤ_[l]) ^ (padicValNat l k + 1) * z) := by
    have h : (x : ℤ_[l]) = y - (l : ℤ_[l]) ^ (m + 1) * z := by rw [hyx]; ring
    push_cast
    rw [h, hy, hms, pow_add]
    ring
  have hd1 : (l : ℤ) ^ s₀ ∣ x - 1 := by
    rw [← PadicInt.pow_p_dvd_int_iff, hx1]
    exact Dvd.intro _ rfl
  have hd2 : ¬ (l : ℤ) ^ (s₀ + 1) ∣ x - 1 := by
    rw [← PadicInt.pow_p_dvd_int_iff, hx1, pow_succ]
    intro h
    have hp0 : (l : ℤ_[l]) ^ s₀ ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    have h3 := (mul_dvd_mul_iff_left hp0).mp h
    have h4 : (l : ℤ_[l]) ∣ (u : ℤ_[l]) := by
      have h5 : (l : ℤ_[l]) ∣ (l : ℤ_[l]) ^ (padicValNat l k + 1) * z :=
        Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero _)) _
      have := dvd_add h3 h5
      simpa using this
    exact PadicInt.prime_p.not_isUnit (isUnit_of_dvd_unit h4 u.isUnit)
  have hcore := Formalism.NG.character_column_kernel_length_bound l s₀ h1 h2 x hd1 hd2 0 k hk
  rw [pow_zero, Nat.sub_zero] at hcore
  have hne : x ^ k - 1 ≠ 0 := by
    intro h0
    rw [h0, padicValInt.zero] at hcore
    omega
  have hA := addVal_int (O := O) l hlu (x ^ k - 1) hne
  rw [hcore] at hA
  obtain ⟨q, hq⟩ : (algebraMap ℤ_[l] O y - (x : O)) ∣ (algebraMap ℤ_[l] O y) ^ k - (x : O) ^ k :=
    sub_dvd_pow_sub_pow _ _ _
  have hyO : algebraMap ℤ_[l] O y - (x : O) = (l : O) ^ (m + 1) * algebraMap ℤ_[l] O z := by
    rw [hyx, map_add, map_mul, map_pow, map_natCast, map_intCast]
    ring
  have hsplit : (algebraMap ℤ_[l] O y) ^ k - 1 =
      ((x ^ k - 1 : ℤ) : O) + (l : O) ^ (m + 1) * (algebraMap ℤ_[l] O z * q) := by
    have : (algebraMap ℤ_[l] O y) ^ k = (x : O) ^ k + (l : O) ^ (m + 1) * algebraMap ℤ_[l] O z * q := by
      rw [← hyO, ← hq]
      ring
    rw [this]
    push_cast
    ring
  obtain ⟨e, he⟩ : ∃ e : ℕ, addVal O (l : O) = (e : ℕ∞) :=
    ⟨(addVal O (l : O)).toNat, (ENat.natCast_toNat (fun h => hl0 (addVal_eq_top_iff.mp h))).symm⟩
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h] at he
      exact absurd (addVal_eq_zero_iff.mp (by simpa using he)) hlu
    · exact h
  have hlt : addVal O ((x ^ k - 1 : ℤ) : O) <
      addVal O ((l : O) ^ (m + 1) * (algebraMap ℤ_[l] O z * q)) := by
    rw [hA, addVal_mul, addVal_pow, he]
    have h6 : ((m : ℕ) : ℕ∞) * (e : ℕ∞) < (m + 1) • (e : ℕ∞) := by
      rw [nsmul_eq_mul]
      have : m * e < (m + 1) * e := by nlinarith
      exact_mod_cast this
    exact lt_of_lt_of_le h6 le_self_add
  rw [hsplit, AddValuation.map_add_eq_of_lt_left _ hlt, hA]

end Del

end Br

/- English proof (translation)
Unfold `EndomorphismIndexBound`. Introduce `Z' hZ' α A hA hcomm h1 h0`. Conclude with `Br.hecke_length_bound_localised D.nd i Z' hZ' α A hA hcomm h1 h0`.
-/
theorem endomorphism_index_bound {D : Formalism.BasicNotions.D7} (i : D.nd.Loc) : EndomorphismIndexBound i := by
  unfold EndomorphismIndexBound
  intro Z' hZ' α A hA hcomm h1 h0
  exact Br.hecke_length_bound_localised D.nd i Z' hZ' α A hA hcomm h1 h0

/- English proof (translation)
Unfold `HodgeTateFromSandwich`. Conclude with `fun i => endomorphism_index_bound i`.
-/
theorem second_statement (D : Formalism.BasicNotions.D7) : HodgeTateFromSandwich D := by
  unfold HodgeTateFromSandwich
  exact fun i => endomorphism_index_bound i

end Formalism.MainNotions.TruncatedSeriesCountingIdentities
