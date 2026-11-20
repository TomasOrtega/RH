import Mathlib

open TensorProduct Module

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ M W _ _ _ _ D R _ F B hRD hFD hBR hBF hnd`. Set `RV : Submodule k ↥D` to `R.comap D.subtype`. Set `T : ↥D →ₗ[k] ↥D` to `F.restrict hFD - LinearMap.id`. Set `Q : ↥D →ₗ[k] ↥D ⧸ RV` to `RV.mkQ ∘ₗ T`. Set `P : W →ₗ[k] Module.Dual k ↥D` to `(B ∘ₗ D.subtype).flip`.

Establish `hP : ∀ w, P w ∈ RV.dualAnnihilator`. Introduce `w`. Rewrite using `[Submodule.mem_dualAnnihilator]`. Introduce `x hx`. Conclude with `hBR x.1 hx w`.

Set `L : W →ₗ[k] Module.Dual k (↥D ⧸ RV)` to `RV.dualCopairing ∘ₗ P.codRestrict RV.dualAnnihilator hP`. Establish `hL : ∀ w (x : ↥D), L w (RV.mkQ x) = B x.1 w` using `fun _ _ => rfl`. Establish `hLinj : Function.Injective L`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `w hw`.

Apply `hnd` to reduce the goal to its premises. Introduce `x hx`. Establish `h` using `LinearMap.congr_fun hw (RV.mkQ ⟨x, hx⟩)`. Rewrite `h` using `[hL, LinearMap.zero_apply]`. Conclude with `h`.

Establish `hLQ : ∀ w, L w ∈ (LinearMap.range Q).dualAnnihilator`. Introduce `w`. Rewrite using `[Submodule.mem_dualAnnihilator]`. Introduce and unpack `_ ⟨x, rfl⟩`. Establish `hTx : ((T x : ↥D) : M) = F x.1 - x.1` using `rfl`.

Use `show L w (RV.mkQ (T x)) = 0`. Rewrite using `[hL, hTx, map_sub, LinearMap.sub_apply, hBF x.1 x.2, sub_self]`. Establish `hW : finrank k W ≤ finrank k (LinearMap.range Q).dualAnnihilator` using `LinearMap.finrank_le_finrank_of_injective (f := L.codRestrict _ hLQ) (fun a b h => hLinj (congrArg Subtype.val h))`. Establish `hker : LinearMap.ker Q = (D ⊓ R.comap (F - LinearMap.id)).comap D.subtype`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : T x ∈ RV` using `(Submodule.Quotient.mk_eq_zero RV).mp h`. Conclude with `⟨x.2, h'⟩`. Introduce `h`.

Conclude with `(Submodule.Quotient.mk_eq_zero RV).mpr h.2`. Establish `h1` using `Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range Q)`. Establish `h2` using `Submodule.finrank_quotient_add_finrank RV`. Establish `h3` using `LinearMap.finrank_range_add_finrank_ker Q`. Establish `h4 : finrank k ↥RV = finrank k ↥R` using `(Submodule.comapSubtypeEquivOfLe hRD).finrank_eq`.

Establish `h5 : finrank k ↥(LinearMap.ker Q) = finrank k ↥(D ⊓ R.comap (F - LinearMap.id))`. Rewrite using `[hker]`. Conclude with `(Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_add_finrank_le_finrank_inf_comap_sub_id :
    ∀ (k : Type) [Field k] (M W : Type) [AddCommGroup M] [Module k M] [AddCommGroup W] [Module k W] (D R : Submodule k M) [FiniteDimensional k ↥D] (F : M →ₗ[k] M) (B : M →ₗ[k] W →ₗ[k] k), R ≤ D → (∀ x ∈ D, F x ∈ D) → (∀ x ∈ R, ∀ w, B x w = 0) → (∀ x ∈ D, ∀ w, B (F x) w = B x w) → (∀ w, (∀ x ∈ D, B x w = 0) → w = 0) → finrank k W + finrank k ↥R ≤ finrank k ↥(D ⊓ R.comap (F - LinearMap.id)) := by
  intro k _ M W _ _ _ _ D R _ F B hRD hFD hBR hBF hnd

  let RV : Submodule k ↥D := R.comap D.subtype
  let T : ↥D →ₗ[k] ↥D := F.restrict hFD - LinearMap.id
  let Q : ↥D →ₗ[k] ↥D ⧸ RV := RV.mkQ ∘ₗ T

  let P : W →ₗ[k] Module.Dual k ↥D := (B ∘ₗ D.subtype).flip
  have hP : ∀ w, P w ∈ RV.dualAnnihilator := by
    intro w
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    exact hBR x.1 hx w
  let L : W →ₗ[k] Module.Dual k (↥D ⧸ RV) :=
    RV.dualCopairing ∘ₗ P.codRestrict RV.dualAnnihilator hP
  have hL : ∀ w (x : ↥D), L w (RV.mkQ x) = B x.1 w := fun _ _ => rfl

  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    apply hnd
    intro x hx
    have h := LinearMap.congr_fun hw (RV.mkQ ⟨x, hx⟩)
    rw [hL, LinearMap.zero_apply] at h
    exact h

  have hLQ : ∀ w, L w ∈ (LinearMap.range Q).dualAnnihilator := by
    intro w
    rw [Submodule.mem_dualAnnihilator]
    rintro _ ⟨x, rfl⟩
    have hTx : ((T x : ↥D) : M) = F x.1 - x.1 := rfl
    show L w (RV.mkQ (T x)) = 0
    rw [hL, hTx, map_sub, LinearMap.sub_apply, hBF x.1 x.2, sub_self]
  have hW : finrank k W ≤ finrank k (LinearMap.range Q).dualAnnihilator :=
    LinearMap.finrank_le_finrank_of_injective (f := L.codRestrict _ hLQ)
      (fun a b h => hLinj (congrArg Subtype.val h))

  have hker : LinearMap.ker Q = (D ⊓ R.comap (F - LinearMap.id)).comap D.subtype := by
    ext x
    constructor
    · intro h
      have h' : T x ∈ RV := (Submodule.Quotient.mk_eq_zero RV).mp h
      exact ⟨x.2, h'⟩
    · intro h
      exact (Submodule.Quotient.mk_eq_zero RV).mpr h.2
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range Q)
  have h2 := Submodule.finrank_quotient_add_finrank RV
  have h3 := LinearMap.finrank_range_add_finrank_ker Q
  have h4 : finrank k ↥RV = finrank k ↥R := (Submodule.comapSubtypeEquivOfLe hRD).finrank_eq
  have h5 : finrank k ↥(LinearMap.ker Q) = finrank k ↥(D ⊓ R.comap (F - LinearMap.id)) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq
  omega

end GlobalTheory
