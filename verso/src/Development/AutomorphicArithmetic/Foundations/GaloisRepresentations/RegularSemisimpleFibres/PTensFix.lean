import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Stabilizer
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SmoothOf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SmoothTensorFactor
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.Parabolic (mem_fixed)

namespace UpperTheory.Gal.InertialTypesAlt.TensorFixedVectors

section Rep

variable {Γ X : Type} [Group Γ] [AddCommGroup X] [Module ℂ X]

private noncomputable def stab (π : Representation ℂ Γ X) (x : X) : Subgroup Γ :=
  _root_.UpperTheory.Reformulated.B.RepresentationVectorStabilizer.stab π x

/- English proof (translation)
Establish `h1 : v - idem hπ hH v ∈ twKer π H 1`. Rewrite using `[← idem_eq_zero_iff hπ hH, map_sub, idem_of_mem hπ hH (idem_mem hπ hH v), sub_self]`. Establish `h3` using `(idem_eq_zero_iff hπ hH).2 (twKer_le_comap π H g hg h1)`. Rewrite `h3` using `[map_sub, map_sub, sub_eq_zero]`. Rewrite using `[h3]`.

Use `idem_of_mem hπ hH (mem_fixed.2 fun u hu => ?_)` and prove the remaining obligations. Establish `hu' : g⁻¹ * u * g ∈ H`. Use `(Subgroup.mem_normalizer_iff.1 (inv_mem hg) u).1 hu` as an intermediate fact. Simplify using `using this`. Establish `h4 : π u (π g (idem hπ hH v)) = π g (π (g⁻¹ * u * g) (idem hπ hH v))`.

Establish `e1 : u * g = g * (g⁻¹ * u * g)` using `by group`. Rewrite using `[← Module.End.mul_apply (π u), ← map_mul, e1, map_mul, Module.End.mul_apply]`. Rewrite using `[h4, mem_fixed.1 (idem_mem hπ hH v) _ hu']`.
-/
private theorem idem_comm [TopologicalSpace Γ] [IsTopologicalGroup Γ] {π : Representation ℂ Γ X}
    (hπ : GlobalTheory.PRep.IsSmooth π) {H : Subgroup Γ} (hH : IsCompact (H : Set Γ)) {g : Γ}
    (hg : g ∈ Subgroup.normalizer (H : Set Γ)) (v : X) :
    idem hπ hH (π g v) = π g (idem hπ hH v) := by
  have h1 : v - idem hπ hH v ∈ twKer π H 1 := by
    rw [← idem_eq_zero_iff hπ hH, map_sub, idem_of_mem hπ hH (idem_mem hπ hH v), sub_self]
  have h3 := (idem_eq_zero_iff hπ hH).2 (twKer_le_comap π H g hg h1)
  rw [map_sub, map_sub, sub_eq_zero] at h3
  rw [h3]
  refine idem_of_mem hπ hH (mem_fixed.2 fun u hu => ?_)
  have hu' : g⁻¹ * u * g ∈ H := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) u).1 hu
    simpa using this
  have h4 : π u (π g (idem hπ hH v)) = π g (π (g⁻¹ * u * g) (idem hπ hH v)) := by
    have e1 : u * g = g * (g⁻¹ * u * g) := by group
    rw [← Module.End.mul_apply (π u), ← map_mul, e1, map_mul, Module.End.mul_apply]
  rw [h4, mem_fixed.1 (idem_mem hπ hH v) _ hu']

end Rep

section Tensor

variable {s : ℕ} {G V : Fin s → Type} [∀ a, Group (G a)] [∀ a, AddCommGroup (V a)] [∀ a, Module ℂ (V a)]

private noncomputable def intersection_update_fsHerm_neg_one (σ : ∀ a, Representation ℂ (G a) (V a)) (a : Fin s) :
    Representation ℂ (G a) (PiTensorProduct ℂ V) :=
  (piTensor σ).comp (MonoidHom.mulSingle G a)

/- English proof (translation)
Use `show piTensor σ (Pi.mulSingle a g) _ = _`. Rewrite using `[piTensor_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Distinguish the cases in `h : b = a`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Pi.mulSingle_eq_of_ne h]`.
-/
private theorem position_tprod (σ : ∀ a, Representation ℂ (G a) (V a)) (a : Fin s) (g : G a) (f : ∀ b, V b) :
    intersection_update_fsHerm_neg_one σ a g (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f a (σ a g (f a))) := by
  show piTensor σ (Pi.mulSingle a g) _ = _
  rw [piTensor_tprod]
  congr 1
  funext b
  by_cases h : b = a
  · subst h; simp
  · simp [h, Pi.mulSingle_eq_of_ne h]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.SmoothTensorFactor.position_smooth σ hσ a`.
-/
private theorem position_smooth [∀ a, TopologicalSpace (G a)] [∀ a, IsTopologicalGroup (G a)] (σ : ∀ a, Representation ℂ (G a) (V a))
    (hσ : ∀ a, GlobalTheory.PRep.IsSmooth (σ a)) (a : Fin s) : GlobalTheory.PRep.IsSmooth (intersection_update_fsHerm_neg_one σ a) :=
  _root_.UpperTheory.Reformulated.B.SmoothTensorFactor.position_smooth σ hσ a

private noncomputable def oneMap (a : Fin s) (e : V a →ₗ[ℂ] V a) : PiTensorProduct ℂ V →ₗ[ℂ] PiTensorProduct ℂ V :=
  PiTensorProduct.map (Function.update (fun b => (LinearMap.id : V b →ₗ[ℂ] V b)) a e)

/- English proof (translation)
Rewrite using `[oneMap, PiTensorProduct.map_tprod]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Distinguish the cases in `h : b = a`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
private theorem oneMap_tprod (a : Fin s) (e : V a →ₗ[ℂ] V a) (f : ∀ b, V b) :
    oneMap a e (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f a (e (f a))) := by
  rw [oneMap, PiTensorProduct.map_tprod]
  congr 1
  funext b
  by_cases h : b = a
  · subst h; simp
  · simp [h]

/- English proof (translation)
Establish `h1 : ∀ x, oneMap a e x ∈ fixed (intersection_update_fsHerm_neg_one σ a) H` using `fun x => by`. Proceed by induction on `x using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r f`. Use `Submodule.smul_mem _ _ ?_ |> fun h => by rw [map_smul]; exact h` and prove the remaining obligations. Rewrite using `[oneMap_tprod]`.

Use `mem_fixed.2 fun u hu => ?_` and prove the remaining obligations. Rewrite using `[position_tprod, Function.update_self, mem_fixed.1 (he (f a)) u hu, Function.update_idem]`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Establish `h2 : ∀ f : ∀ b, V b, (twKer (σ a) H 1).map ((PiTensorProduct.tprod ℂ).toLinearMap f a) ≤ twKer (intersection_update_fsHerm_neg_one σ a) H 1` using `fun f => by`.

Rewrite using `[Submodule.map_le_iff_le_comap]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨n, v, rfl⟩`. Use `Submodule.subset_span ⟨n, PiTensorProduct.tprod ℂ (Function.update f a v), ?_⟩` and prove the remaining obligations. Simplify using `[MultilinearMap.toLinearMap, position_tprod]`.

Establish `h3 : ∀ x, x - oneMap a e x ∈ twKer (intersection_update_fsHerm_neg_one σ a) H 1` using `fun x => by`. Proceed by induction on `x using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r f`. Rewrite using `[map_smul, ← smul_sub]`. Use `Submodule.smul_mem _ _ (h2 f ⟨_, hk (f a), ?_⟩)` and prove the remaining obligations.

Rewrite using `[oneMap_tprod, map_sub]`. Simplify using `[MultilinearMap.toLinearMap]`. Consider the case `add x y hx hy`. Rewrite using `[map_add, add_sub_add_comm]`. Conclude with `add_mem hx hy`.

Establish `h4` using `Submodule.disjoint_def.1 (isCompl_fixed_twKer (position_smooth σ hσ a) hH).disjoint (w - oneMap a e w) (sub_mem hw (h1 w)) (h3 w)`. Conclude with `(sub_eq_zero.1 h4).symm`.
-/
private theorem oneMap_fix [∀ a, TopologicalSpace (G a)] [∀ a, IsTopologicalGroup (G a)]
    (σ : ∀ a, Representation ℂ (G a) (V a)) (hσ : ∀ a, GlobalTheory.PRep.IsSmooth (σ a)) (a : Fin s)
    {H : Subgroup (G a)} (hH : IsCompact (H : Set (G a))) (e : V a →ₗ[ℂ] V a)
    (he : ∀ v, e v ∈ fixed (σ a) H) (hk : ∀ v, v - e v ∈ twKer (σ a) H 1)
    {w : PiTensorProduct ℂ V} (hw : w ∈ fixed (intersection_update_fsHerm_neg_one σ a) H) : oneMap a e w = w := by
  have h1 : ∀ x, oneMap a e x ∈ fixed (intersection_update_fsHerm_neg_one σ a) H := fun x => by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      refine Submodule.smul_mem _ _ ?_ |> fun h => by rw [map_smul]; exact h
      rw [oneMap_tprod]
      refine mem_fixed.2 fun u hu => ?_
      rw [position_tprod, Function.update_self, mem_fixed.1 (he (f a)) u hu, Function.update_idem]
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  have h2 : ∀ f : ∀ b, V b, (twKer (σ a) H 1).map
      ((PiTensorProduct.tprod ℂ).toLinearMap f a) ≤ twKer (intersection_update_fsHerm_neg_one σ a) H 1 := fun f => by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, v, rfl⟩
    refine Submodule.subset_span ⟨n, PiTensorProduct.tprod ℂ (Function.update f a v), ?_⟩
    simp [MultilinearMap.toLinearMap, position_tprod]
  have h3 : ∀ x, x - oneMap a e x ∈ twKer (intersection_update_fsHerm_neg_one σ a) H 1 := fun x => by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      rw [map_smul, ← smul_sub]
      refine Submodule.smul_mem _ _ (h2 f ⟨_, hk (f a), ?_⟩)
      rw [oneMap_tprod, map_sub]
      simp [MultilinearMap.toLinearMap]
    | add x y hx hy =>
      rw [map_add, add_sub_add_comm]; exact add_mem hx hy
  have h4 := Submodule.disjoint_def.1 (isCompl_fixed_twKer (position_smooth σ hσ a) hH).disjoint
    (w - oneMap a e w) (sub_mem hw (h1 w)) (h3 w)
  exact (sub_eq_zero.1 h4).symm

/- English proof (translation)
Establish `key : ∀ S : Finset (Fin s), PiTensorProduct.map (fun b => if b ∈ S then e b else (LinearMap.id : V b →ₗ[ℂ] V b)) w = w` using `fun S => by`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp [PiTensorProduct.map_id]`. Consider the case `insert a S ha ih`. Establish `e1 : (fun b => if b ∈ insert a S then e b else (LinearMap.id : V b →ₗ[ℂ] V b)) = fun b => (if b ∈ S then e b else (LinearMap.id : V b →ₗ[ℂ] V b)) ∘ₗ Function.update (fun b => (LinearMap.id : V b →ₗ[ℂ] V b)) a (e a) b`.

Use function extensionality and compare the values at `b`. Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Simplify using `[ha]`. Simplify using `[hb]`.

Rewrite using `[e1, PiTensorProduct.map_comp, LinearMap.comp_apply]`. Use `h a` as an intermediate fact. Rewrite `this` using `[oneMap]`. Rewrite using `[this, ih]`. Simplify using `using key Finset.univ`.
-/
private theorem map_fix (e : ∀ a, V a →ₗ[ℂ] V a) (w : PiTensorProduct ℂ V)
    (h : ∀ a, oneMap a (e a) w = w) : PiTensorProduct.map e w = w := by
  have key : ∀ S : Finset (Fin s),
      PiTensorProduct.map (fun b => if b ∈ S then e b else (LinearMap.id : V b →ₗ[ℂ] V b)) w = w := fun S => by
    induction S using Finset.induction_on with
    | empty => simp [PiTensorProduct.map_id]
    | insert a S ha ih =>
      have e1 : (fun b => if b ∈ insert a S then e b else (LinearMap.id : V b →ₗ[ℂ] V b)) =
          fun b => (if b ∈ S then e b else (LinearMap.id : V b →ₗ[ℂ] V b)) ∘ₗ
            Function.update (fun b => (LinearMap.id : V b →ₗ[ℂ] V b)) a (e a) b := by
        funext b
        by_cases hb : b = a
        · subst hb; simp [ha]
        · simp [hb]
      rw [e1, PiTensorProduct.map_comp, LinearMap.comp_apply]
      have := h a
      rw [oneMap] at this
      rw [this, ih]
  simpa using key Finset.univ

end Tensor

end UpperTheory.Gal.InertialTypesAlt.TensorFixedVectors

open UpperTheory.Gal.InertialTypesAlt.TensorFixedVectors in
/- English proof (translation)
Introduce `k _ _ _ _ s d V _ _ σ hσ`. Establish `hK : ∀ a, IsCompact (KOne k (Fin (d a)) : Set (GL (Fin (d a)) k))` using `fun a => levelPre_bot (k := k) (n := Fin (d a)) ▸ isCompact_levelPre ⊥`. Set `e : ∀ a, V a →ₗ[ℂ] V a` to `fun a => idem (hσ a) (hK a)`. Set `pr : ∀ a, V a →ₗ[ℂ] fixed (σ a) (KOne k (Fin (d a)))` to `fun a => (e a).codRestrict _ (idem_mem (hσ a) (hK a))`. Use `⟨PiTensorProduct.map pr, fun x w => ?_, fun w hw h0 => ?_⟩` and prove the remaining obligations.

Proceed by induction on `w using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r f`. Simplify using `only [map_smul, piTensor_tprod, PiTensorProduct.map_tprod]`. Use `congr 2`. Use function extensionality and compare the values at `a`.

Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[redLevi_apply, levelZero_apply]`. Conclude with `idem_comm (hσ a) (hK a) (KO_le_normalizer (x.2 a trivial)) (f a)`. Consider the case `add x' y hx hy => simp only [map_add, hx, hy]`. Establish `hk : ∀ a v, v - e a v ∈ twKer (σ a) (KOne k (Fin (d a))) 1` using `fun a v => by`.

Rewrite using `[← idem_eq_zero_iff (hσ a) (hK a), map_sub, idem_of_mem (hσ a) (hK a) (idem_mem (hσ a) (hK a) v), sub_self]`. Establish `h1 : ∀ a, oneMap a (e a) w = w` using `fun a => oneMap_fix σ hσ a (hK a) (e a) (idem_mem (hσ a) (hK a)) (hk a) (mem_fixed.2 fun u hu => mem_fixed.1 hw (Pi.mulSingle a u) fun b _ => by`. Distinguish the cases in `h : b = a`. Substitute `h` using the available equality. Simplify using `using hu`.

Simplify `one_mem _)` using `[Pi.mulSingle_eq_of_ne h]`. Establish `h2` using `map_fix e w h1`. Establish `h3 : PiTensorProduct.map e = PiTensorProduct.map (fun a => (fixed (σ a) (KOne k (Fin (d a)))).subtype) ∘ₗ PiTensorProduct.map pr`. Rewrite using `[← PiTensorProduct.map_comp]`. Both sides reduce to the same expression.

Rewrite using `[← h2, h3, LinearMap.comp_apply, h0, map_zero]`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.tensFix :
    TensFix := by
  intro k _ _ _ _ s d V _ _ σ hσ
  have hK : ∀ a, IsCompact (KOne k (Fin (d a)) : Set (GL (Fin (d a)) k)) := fun a =>
    levelPre_bot (k := k) (n := Fin (d a)) ▸ isCompact_levelPre ⊥
  let e : ∀ a, V a →ₗ[ℂ] V a := fun a => idem (hσ a) (hK a)
  let pr : ∀ a, V a →ₗ[ℂ] fixed (σ a) (KOne k (Fin (d a))) := fun a =>
    (e a).codRestrict _ (idem_mem (hσ a) (hK a))
  refine ⟨PiTensorProduct.map pr, fun x w => ?_, fun w hw h0 => ?_⟩
  · induction w using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      simp only [map_smul, piTensor_tprod, PiTensorProduct.map_tprod]
      congr 2
      funext a
      refine Subtype.ext ?_
      rw [redLevi_apply, levelZero_apply]
      exact idem_comm (hσ a) (hK a) (KO_le_normalizer (x.2 a trivial)) (f a)
    | add x' y hx hy => simp only [map_add, hx, hy]
  · have hk : ∀ a v, v - e a v ∈ twKer (σ a) (KOne k (Fin (d a))) 1 := fun a v => by
      rw [← idem_eq_zero_iff (hσ a) (hK a), map_sub, idem_of_mem (hσ a) (hK a) (idem_mem (hσ a) (hK a) v), sub_self]
    have h1 : ∀ a, oneMap a (e a) w = w := fun a =>
      oneMap_fix σ hσ a (hK a) (e a) (idem_mem (hσ a) (hK a)) (hk a) (mem_fixed.2 fun u hu =>
        mem_fixed.1 hw (Pi.mulSingle a u) fun b _ => by
          by_cases h : b = a
          · subst h; simpa using hu
          · simpa [Pi.mulSingle_eq_of_ne h] using one_mem _)
    have h2 := map_fix e w h1
    have h3 : PiTensorProduct.map e =
        PiTensorProduct.map (fun a => (fixed (σ a) (KOne k (Fin (d a)))).subtype) ∘ₗ PiTensorProduct.map pr := by
      rw [← PiTensorProduct.map_comp]
      rfl
    rw [← h2, h3, LinearMap.comp_apply, h0, map_zero]
