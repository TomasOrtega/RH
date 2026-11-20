import Formalism.LogFactorialIndices.StatementIdx
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ChainLength
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPowSmulMem

open scoped Pointwise

noncomputable section

namespace Formalism.LatticeIndexTer.subgroupData

variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.JointEigenvalueBoundsFromAnyDatum.length_chain hAB hBC`.
-/
theorem length_chain' {A B C : Submodule O X} (hAB : A ≤ B) (hBC : B ≤ C) :
    Module.length O (C ⧸ A.comap C.subtype) =
      Module.length O (B ⧸ A.comap B.subtype) + Module.length O (C ⧸ B.comap C.subtype) :=
  _root_.UpperTheory.Reformulated.B.JointEigenvalueBoundsFromAnyDatum.length_chain hAB hBC

/- English proof (translation)
Set `f : (S ⧸ B.comap S.subtype) →ₗ[O] (T ⧸ A.comap T.subtype)` to `Submodule.mapQ _ _ (Submodule.inclusion hST) (fun x hx => by`. Simplify using `only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_inclusion] at hx ⊢`. Conclude with `hBA hx)`. Apply `Module.length_le_of_injective f` to reduce the goal to its premises. Introduce `x y hxy`.

Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Simplify using `only [f, Submodule.mapQ_apply] at hxy`. Rewrite `hxy`, the goal using `[Submodule.Quotient.eq]`. Simplify using `only [Submodule.mem_comap, Submodule.coe_subtype, map_sub, Submodule.coe_inclusion] at hxy ⊢`.

Conclude with `hSA (Submodule.mem_inf.mpr ⟨S.sub_mem x.2 y.2, hxy⟩)`.
-/
theorem length_le_of_le {S T A B : Submodule O X} (hST : S ≤ T) (hBA : B ≤ A)
    (hSA : S ⊓ A ≤ B) :
    Module.length O (S ⧸ B.comap S.subtype) ≤ Module.length O (T ⧸ A.comap T.subtype) := by
  let f : (S ⧸ B.comap S.subtype) →ₗ[O] (T ⧸ A.comap T.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hST) (fun x hx => by
      simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_inclusion] at hx ⊢
      exact hBA hx)
  apply Module.length_le_of_injective f
  intro x y hxy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [f, Submodule.mapQ_apply] at hxy
  rw [Submodule.Quotient.eq] at hxy ⊢
  simp only [Submodule.mem_comap, Submodule.coe_subtype, map_sub, Submodule.coe_inclusion]
    at hxy ⊢
  exact hSA (Submodule.mem_inf.mpr ⟨S.sub_mem x.2 y.2, hxy⟩)

/- English proof (translation)
Set `g : (S ⧸ B.comap S.subtype) →ₗ[O] (S ⧸ A.comap S.subtype)` to `Submodule.mapQ _ _ LinearMap.id (fun x hx => by simpa using hBA hx)`. Apply `Module.length_le_of_surjective g` to reduce the goal to its premises. Introduce `z`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Conclude with `⟨Submodule.Quotient.mk z, rfl⟩`.
-/
theorem length_le_of_ge {S A B : Submodule O X} (hBA : B ≤ A) :
    Module.length O (S ⧸ A.comap S.subtype) ≤ Module.length O (S ⧸ B.comap S.subtype) := by
  let g : (S ⧸ B.comap S.subtype) →ₗ[O] (S ⧸ A.comap S.subtype) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => by simpa using hBA hx)
  apply Module.length_le_of_surjective g
  intro z
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨Submodule.Quotient.mk z, rfl⟩

/- English proof (translation)
Unfold `qlen`. Rewrite using `[Module.length_eq_zero_iff]`. Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ a`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective _ b`.

Rewrite using `[Submodule.Quotient.eq]`. Conclude with `h (a - b).2`.
-/
theorem qlen_eq_zero {A B : Submodule O X} (h : A ≤ B) : qlen O X A B = 0 := by
  unfold qlen
  rw [Module.length_eq_zero_iff]
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [Submodule.Quotient.eq]
  exact h (a - b).2

/- English proof (translation)
Use `show Module.length O (A ⧸ B.comap A.subtype) ≠ ⊤`. Establish `: Module.Finite O A` using `Module.Finite.iff_fg.mpr hA`. Take `⟨n, b⟩` from `Module.basisOfFiniteTypeTorsionFree' (R := O) (M := A)`. Set `ψ : (Fin n → O) →ₗ[O] A ⧸ B.comap A.subtype` to `(B.comap A.subtype).mkQ ∘ₗ b.equivFun.symm.toLinearMap`. Establish `hψ : Function.Surjective ψ` using `(Submodule.mkQ_surjective _).comp b.equivFun.symm.surjective`.

Set `P : Submodule O (Fin n → O)` to `Submodule.pi Set.univ (fun _ => Ideal.span {ϖ ^ k})`. Establish `hP : P ≤ LinearMap.ker ψ`. Introduce `x hx`. Use `choose y hy using fun i => Ideal.mem_span_singleton.mp (Submodule.mem_pi.mp hx i (Set.mem_univ i))`. Establish `hxy : x = ϖ ^ k • y` using `funext fun i => by simp [hy i]`.

Rewrite using `[LinearMap.mem_ker, hxy, map_smul]`. Use `set m : A := b.equivFun.symm y`. Rewrite using `[show ψ y = Submodule.Quotient.mk m from rfl, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]`. Simplify using `only [Submodule.coe_subtype, SetLike.val_smul]`. Conclude with `hk _ m.2`.

Establish `hsurj : Function.Surjective (P.liftQ ψ hP)`. Introduce `z`. Take `⟨w, hw⟩` from `hψ z`. Conclude with `⟨Submodule.Quotient.mk w, hw⟩`. Use `ne_top_of_le_ne_top ?_ (Module.length_le_of_surjective _ hsurj)` and prove the remaining obligations.

Rewrite using `[(Submodule.quotientPi (fun _ : Fin n => Ideal.span {ϖ ^ k})).length_eq, Module.length_pi]`. Establish `: Ideal.span {ϖ ^ k} = IsLocalRing.maximalIdeal O ^ k`. Rewrite using `[hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]`. Rewrite using `[this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]`. Simplify using `only [ENat.card_eq_coe_fintype_card, Fintype.card_fin, ne_eq]`.

Rewrite using `[← Nat.cast_mul]`. Conclude with `ENat.natCast_ne_top _`.
-/
theorem qlen_ne_top_of_pow {O X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup X] [Module O X] [Module.IsTorsionFree O X] (ϖ : O) (hϖ : Irreducible ϖ) (k : ℕ)
    (A B : Submodule O X) (hA : A.FG) (hk : ∀ a ∈ A, ϖ ^ k • a ∈ B) : qlen O X A B ≠ ⊤ := by
  show Module.length O (A ⧸ B.comap A.subtype) ≠ ⊤
  have : Module.Finite O A := Module.Finite.iff_fg.mpr hA
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := O) (M := A)
  let ψ : (Fin n → O) →ₗ[O] A ⧸ B.comap A.subtype :=
    (B.comap A.subtype).mkQ ∘ₗ b.equivFun.symm.toLinearMap
  have hψ : Function.Surjective ψ :=
    (Submodule.mkQ_surjective _).comp b.equivFun.symm.surjective
  let P : Submodule O (Fin n → O) := Submodule.pi Set.univ (fun _ => Ideal.span {ϖ ^ k})
  have hP : P ≤ LinearMap.ker ψ := by
    intro x hx
    choose y hy using fun i =>
      Ideal.mem_span_singleton.mp (Submodule.mem_pi.mp hx i (Set.mem_univ i))
    have hxy : x = ϖ ^ k • y := funext fun i => by simp [hy i]
    rw [LinearMap.mem_ker, hxy, map_smul]
    set m : A := b.equivFun.symm y
    rw [show ψ y = Submodule.Quotient.mk m from rfl, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    simp only [Submodule.coe_subtype, SetLike.val_smul]
    exact hk _ m.2
  have hsurj : Function.Surjective (P.liftQ ψ hP) := by
    intro z
    obtain ⟨w, hw⟩ := hψ z
    exact ⟨Submodule.Quotient.mk w, hw⟩
  refine ne_top_of_le_ne_top ?_ (Module.length_le_of_surjective _ hsurj)
  rw [(Submodule.quotientPi (fun _ : Fin n => Ideal.span {ϖ ^ k})).length_eq, Module.length_pi]
  have : Ideal.span {ϖ ^ k} = IsLocalRing.maximalIdeal O ^ k := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin, ne_eq]
  rw [← Nat.cast_mul]
  exact ENat.natCast_ne_top _

end Formalism.LatticeIndexTer.subgroupData

namespace Formalism.LatticeIndexTer

open Formalism.LatticeIndexTer.subgroupData

/- English proof (translation)
Introduce `O K X _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ F M Θ hM hΘ W MW ΘW`. Establish `hΘM : Θ ≤ M` using `fun x hx => by`. Take `⟨y, hy, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hΘ hx)`. Conclude with `M.smul_mem _ hy`. Establish `hMW : MW ≤ M` using `inf_le_left`.

Establish `h1 : Θ ≤ Θ ⊔ MW` using `le_sup_left`. Establish `h2 : Θ ⊔ MW ≤ M` using `sup_le hΘM hMW`. Rewrite using `[length_chain' h1 h2]`. Establish `hA : Module.length O (MW ⧸ ΘW.comap MW.subtype) ≤ Module.length O (↥(Θ ⊔ MW) ⧸ Θ.comap (Θ ⊔ MW).subtype)` using `length_le_of_le le_sup_right inf_le_left (fun x hx => Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hx).2, (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx).1).2⟩)`. Use `add_le_add hA ?_` and prove the remaining obligations.

Establish `: Module.IsTorsionFree O (X ⧸ W)` using `.trans_faithfulSMul O K (X ⧸ W)`. Set `q : X →ₗ[O] X ⧸ W` to `W.mkQ.restrictScalars O`. Set `N : Submodule O (X ⧸ W)` to `M.map q`. Establish `: Module.Finite O N` using `Module.Finite.iff_fg.mpr (hM.1.map q)`. Take `⟨n, b⟩` from `Module.basisOfFiniteTypeTorsionFree' (R := O) (M := N)`.

Establish `hNle : ∀ y : N, (y : X ⧸ W) ∈ Submodule.span K (Set.range fun i => ((b i : N) : X ⧸ W))`. Introduce `y`. Rewrite using `[← b.sum_repr y]`. Simplify using `only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Establish `hspan : Submodule.span K (Set.range fun i => ((b i : N) : X ⧸ W)) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `z -`. Take `⟨x, rfl⟩` from `W.mkQ_surjective z`. Establish `hx : x ∈ Submodule.span K (M : Set X)` using `hM.2 ▸ Submodule.mem_top`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact hNle ⟨q y, Submodule.mem_map_of_mem hy⟩`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`.

Consider the case `smul a y _ hy => rw [map_smul]`. Conclude with `Submodule.smul_mem _ a hy`. Establish `hd : Module.finrank K X - Module.finrank K W ≤ n`. Establish `e1` using `Submodule.finrank_quotient_add_finrank W`. Establish `e2` using `finrank_range_le_card (R := K) (fun i => ((b i : N) : X ⧸ W))`.

Rewrite `e2` using `[Set.finrank, hspan, finrank_top, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Set `I : Ideal O` to `Ideal.span {ϖ ^ F}`. Set `φ : M →ₗ[O] N` to `q.submoduleMap M`. Set `π : (Fin n → O) →ₗ[O] (Fin n → O ⧸ I)` to `LinearMap.pi fun i => I.mkQ ∘ₗ LinearMap.proj i`.

Set `ψ : M →ₗ[O] (Fin n → O ⧸ I)` to `π ∘ₗ b.equivFun.toLinearMap ∘ₗ φ`. Establish `hψ : Function.Surjective ψ`. Introduce `y`. Use `choose c hc using fun i => Submodule.Quotient.mk_surjective I (y i)`. Take `⟨m, hm⟩` from `LinearMap.submoduleMap_surjective q M (b.equivFun.symm c)`.

Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `hm' : φ m = b.equivFun.symm c` using `hm`. Use function extensionality and compare the values at `i`. Simplify using `only [ψ, LinearMap.comp_apply, hm', LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]`. Simplify using `only [π, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Submodule.mkQ_apply]`.

Conclude with `hc i`. Establish `hker : (Θ ⊔ MW).comap M.subtype ≤ LinearMap.ker ψ`. Introduce `m hm`. Rewrite `hm` using `[Submodule.mem_comap]`. Take `⟨θ, hθ, w, hw, hsum⟩` from `Submodule.mem_sup.mp hm`.

Establish `hm' : m = ⟨θ, hΘM hθ⟩ + ⟨w, hMW hw⟩` using `Subtype.ext (by simp [hsum])`. Rewrite using `[LinearMap.mem_ker, hm', map_add]`. Establish `hw0 : φ ⟨w, hMW hw⟩ = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [φ, ZeroMemClass.coe_zero]`.

Conclude with `(Submodule.Quotient.mk_eq_zero W).mpr (Submodule.mem_inf.mp hw).2`. Establish `hw0' : ψ ⟨w, hMW hw⟩ = 0`. Simplify using `only [ψ, LinearMap.comp_apply, hw0, map_zero]`. Establish `hθ0 : ψ ⟨θ, hΘM hθ⟩ = 0`. Take `⟨y, hy, hyθ⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hΘ hθ)`.

Establish `hsm : (⟨θ, hΘM hθ⟩ : M) = ϖ ^ F • ⟨y, hy⟩` using `Subtype.ext hyθ.symm`. Rewrite using `[hsm, map_smul]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, Pi.zero_apply]`. Take `⟨c, hc⟩` from `Submodule.Quotient.mk_surjective I (ψ ⟨y, hy⟩ i)`.

Rewrite using `[← hc, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Rewrite using `[hθ0, hw0', add_zero]`. Establish `hsurj : Function.Surjective (((Θ ⊔ MW).comap M.subtype).liftQ ψ hker)`. Introduce `z`.

Take `⟨m, hm⟩` from `hψ z`. Conclude with `⟨Submodule.Quotient.mk m, hm⟩`. Establish `hlen : Module.length O (Fin n → O ⧸ I) = ((n * F : ℕ) : ℕ∞)`. Rewrite using `[Module.length_pi]`. Establish `: I = IsLocalRing.maximalIdeal O ^ F`.

Rewrite using `[hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]`. Rewrite using `[this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]`. Simplify using the standard rewrite rules. Use `le_trans ?_ (Module.length_le_of_surjective _ hsurj)` and prove the remaining obligations. Rewrite using `[hlen]`.

Conclude with `(by rw [Nat.mul_comm n]; exact Nat.mul_le_mul_left F hd)` after adjusting the coercions.
-/
theorem subspace_lattice_index : SubspaceIndex := by
  intro O K X _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ F M Θ hM hΘ W MW ΘW
  have hΘM : Θ ≤ M := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hΘ hx)
    exact M.smul_mem _ hy
  have hMW : MW ≤ M := inf_le_left
  have h1 : Θ ≤ Θ ⊔ MW := le_sup_left
  have h2 : Θ ⊔ MW ≤ M := sup_le hΘM hMW
  rw [length_chain' h1 h2]
  have hA : Module.length O (MW ⧸ ΘW.comap MW.subtype) ≤
      Module.length O (↥(Θ ⊔ MW) ⧸ Θ.comap (Θ ⊔ MW).subtype) :=
    length_le_of_le le_sup_right inf_le_left (fun x hx =>
      Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hx).2,
        (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx).1).2⟩)
  refine add_le_add hA ?_

  have : Module.IsTorsionFree O (X ⧸ W) := .trans_faithfulSMul O K (X ⧸ W)
  let q : X →ₗ[O] X ⧸ W := W.mkQ.restrictScalars O
  let N : Submodule O (X ⧸ W) := M.map q
  have : Module.Finite O N := Module.Finite.iff_fg.mpr (hM.1.map q)
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := O) (M := N)
  have hNle : ∀ y : N, (y : X ⧸ W) ∈ Submodule.span K (Set.range fun i => ((b i : N) : X ⧸ W)) := by
    intro y
    rw [← b.sum_repr y]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span K (Set.range fun i => ((b i : N) : X ⧸ W)) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨x, rfl⟩ := W.mkQ_surjective z
    have hx : x ∈ Submodule.span K (M : Set X) := hM.2 ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact hNle ⟨q y, Submodule.mem_map_of_mem hy⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ a hy
  have hd : Module.finrank K X - Module.finrank K W ≤ n := by
    have e1 := Submodule.finrank_quotient_add_finrank W
    have e2 := finrank_range_le_card (R := K) (fun i => ((b i : N) : X ⧸ W))
    rw [Set.finrank, hspan, finrank_top, Fintype.card_fin] at e2
    omega

  let I : Ideal O := Ideal.span {ϖ ^ F}
  let φ : M →ₗ[O] N := q.submoduleMap M
  let π : (Fin n → O) →ₗ[O] (Fin n → O ⧸ I) := LinearMap.pi fun i => I.mkQ ∘ₗ LinearMap.proj i
  let ψ : M →ₗ[O] (Fin n → O ⧸ I) := π ∘ₗ b.equivFun.toLinearMap ∘ₗ φ
  have hψ : Function.Surjective ψ := by
    intro y
    choose c hc using fun i => Submodule.Quotient.mk_surjective I (y i)
    obtain ⟨m, hm⟩ := LinearMap.submoduleMap_surjective q M (b.equivFun.symm c)
    refine ⟨m, ?_⟩
    have hm' : φ m = b.equivFun.symm c := hm
    funext i
    simp only [ψ, LinearMap.comp_apply, hm', LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    simp only [π, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Submodule.mkQ_apply]
    exact hc i
  have hker : (Θ ⊔ MW).comap M.subtype ≤ LinearMap.ker ψ := by
    intro m hm
    rw [Submodule.mem_comap] at hm
    obtain ⟨θ, hθ, w, hw, hsum⟩ := Submodule.mem_sup.mp hm
    have hm' : m = ⟨θ, hΘM hθ⟩ + ⟨w, hMW hw⟩ := Subtype.ext (by simp [hsum])
    rw [LinearMap.mem_ker, hm', map_add]
    have hw0 : φ ⟨w, hMW hw⟩ = 0 := by
      apply Subtype.ext
      simp only [φ, ZeroMemClass.coe_zero]
      exact (Submodule.Quotient.mk_eq_zero W).mpr (Submodule.mem_inf.mp hw).2
    have hw0' : ψ ⟨w, hMW hw⟩ = 0 := by
      simp only [ψ, LinearMap.comp_apply, hw0, map_zero]
    have hθ0 : ψ ⟨θ, hΘM hθ⟩ = 0 := by
      obtain ⟨y, hy, hyθ⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hΘ hθ)
      have hsm : (⟨θ, hΘM hθ⟩ : M) = ϖ ^ F • ⟨y, hy⟩ := Subtype.ext hyθ.symm
      rw [hsm, map_smul]
      funext i
      simp only [Pi.smul_apply, Pi.zero_apply]
      obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective I (ψ ⟨y, hy⟩ i)
      rw [← hc, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [hθ0, hw0', add_zero]
  have hsurj : Function.Surjective (((Θ ⊔ MW).comap M.subtype).liftQ ψ hker) := by
    intro z
    obtain ⟨m, hm⟩ := hψ z
    exact ⟨Submodule.Quotient.mk m, hm⟩
  have hlen : Module.length O (Fin n → O ⧸ I) = ((n * F : ℕ) : ℕ∞) := by
    rw [Module.length_pi]
    have : I = IsLocalRing.maximalIdeal O ^ F := by
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    rw [this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    simp
  refine le_trans ?_ (Module.length_le_of_surjective _ hsurj)
  rw [hlen]
  exact_mod_cast (by rw [Nat.mul_comm n]; exact Nat.mul_le_mul_left F hd)

/- English proof (translation)
Introduce `O K X _ _ _ _ _ _ _ _ _ _ _ e he A Θ hA hΘ hΘA V₀`. Establish `hfin : qlen O X A Θ ≠ ⊤` using `h1 O K X A Θ hA hΘ`. Establish `hQ'P : Θ ⊓ V₀ ≤ A ⊓ V₀` using `inf_le_inf_right _ hΘA`. Establish `hPQ' : qlen O X (A ⊓ V₀) (Θ ⊓ V₀) ≤ qlen O X A Θ` using `length_le_of_le inf_le_left inf_le_left (fun x hx => Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hx).2, (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx).1).2⟩)`. Establish `hfin' : qlen O X (A ⊓ V₀) (Θ ⊓ V₀) ≠ ⊤` using `ne_top_of_le_ne_top hfin hPQ'`.

Establish `hidx1 : idx O X A Θ = ((qlen O X A Θ).toNat : ℤ)`. Simplify using `[idx, qlen_eq_zero hΘA]`. Establish `hidx2 : idx O X (A ⊓ V₀) (Θ ⊓ V₀) = ((qlen O X (A ⊓ V₀) (Θ ⊓ V₀)).toNat : ℤ)`. Simplify using `[idx, qlen_eq_zero hQ'P]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hidx1, hidx2]`. Conclude with `ENat.toNat_le_toNat hPQ' hfin` after adjusting the coercions. Rewrite using `[hidx2]`. Establish `hQ'Q : Θ ⊓ V₀ ≤ Θ.map (e.restrictScalars O)`. Introduce `x hx`.

Establish `hxΘ : x ∈ Θ` using `(Submodule.mem_inf.mp hx).1`. Establish `hxV : x ∈ LinearMap.range e` using `(Submodule.mem_inf.mp hx).2`. Take `⟨y, rfl⟩` from `LinearMap.mem_range.mp hxV`. Use `Submodule.mem_map.mpr ⟨e y, hxΘ, ?_⟩` and prove the remaining obligations. Use `LinearMap.congr_fun he y` as an intermediate fact.

Simplify using `using this`. Establish `hle : qlen O X (A ⊓ V₀) (Θ.map (e.restrictScalars O)) ≤ qlen O X (A ⊓ V₀) (Θ ⊓ V₀)` using `length_le_of_ge hQ'Q`. Use `ENat.toNat_le_toNat hle hfin'` as an intermediate fact. Unfold `idx`. Use linear arithmetic over natural numbers and integers.
-/
theorem goodIndex_of_latFinite (h1 : LatFinite) : GoodIndex := by
  intro O K X _ _ _ _ _ _ _ _ _ _ _ e he A Θ hA hΘ hΘA V₀
  have hfin : qlen O X A Θ ≠ ⊤ := h1 O K X A Θ hA hΘ
  have hQ'P : Θ ⊓ V₀ ≤ A ⊓ V₀ := inf_le_inf_right _ hΘA
  have hPQ' : qlen O X (A ⊓ V₀) (Θ ⊓ V₀) ≤ qlen O X A Θ :=
    length_le_of_le inf_le_left inf_le_left (fun x hx =>
      Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hx).2,
        (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx).1).2⟩)
  have hfin' : qlen O X (A ⊓ V₀) (Θ ⊓ V₀) ≠ ⊤ := ne_top_of_le_ne_top hfin hPQ'
  have hidx1 : idx O X A Θ = ((qlen O X A Θ).toNat : ℤ) := by
    simp [idx, qlen_eq_zero hΘA]
  have hidx2 : idx O X (A ⊓ V₀) (Θ ⊓ V₀) = ((qlen O X (A ⊓ V₀) (Θ ⊓ V₀)).toNat : ℤ) := by
    simp [idx, qlen_eq_zero hQ'P]
  refine ⟨?_, ?_⟩
  · rw [hidx1, hidx2]
    exact_mod_cast ENat.toNat_le_toNat hPQ' hfin
  · rw [hidx2]
    have hQ'Q : Θ ⊓ V₀ ≤ Θ.map (e.restrictScalars O) := by
      intro x hx
      have hxΘ : x ∈ Θ := (Submodule.mem_inf.mp hx).1
      have hxV : x ∈ LinearMap.range e := (Submodule.mem_inf.mp hx).2
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hxV
      refine Submodule.mem_map.mpr ⟨e y, hxΘ, ?_⟩
      have := LinearMap.congr_fun he y
      simpa using this
    have hle : qlen O X (A ⊓ V₀) (Θ.map (e.restrictScalars O)) ≤ qlen O X (A ⊓ V₀) (Θ ⊓ V₀) :=
      length_le_of_ge hQ'Q
    have := ENat.toNat_le_toNat hle hfin'
    unfold idx
    omega

/- English proof (translation)
The claim follows from `goodIndex_of_latFinite h1`.
-/
theorem goodIndex_of (h1 : LatFinite) (_h2 : IdxAdd) : GoodIndex := goodIndex_of_latFinite h1

end Formalism.LatticeIndexTer
