import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.TopLeCopiesSelf

open GlobalTheory.PRep Matrix UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
open scoped ComplexOrder

/- English proof (translation)
Introduce `k G V _ _ _ _ _ _ _ ρ K χ hK hχ v hv`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK`. Set `S : Subgroup K` to `{ carrier := {x | ρ (x : G) v = v ∧ χ x = 1} mul_mem' := by`. Introduce and unpack `x y ⟨hx, hx'⟩ ⟨hy, hy'⟩`. Use `⟨?_, by rw [map_mul, hx', hy', mul_one]⟩` and prove the remaining obligations.

Rewrite using `[Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]`. Use the proof step `one_mem' := ⟨by simp, map_one χ⟩`. Use the proof step `inv_mem' := by`. Introduce and unpack `x ⟨hx, hx'⟩`. Use `⟨?_, by rw [map_inv, hx', inv_one]⟩` and prove the remaining obligations.

Use `conv_lhs => rw [← hx]`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using `}`. Establish `hSo : IsOpen (S : Set K)` using `(hv.preimage continuous_subtype_val).inter hχ`. Use `haveI : Finite (K ⧸ S) := S.quotient_finite_of_isOpen hSo`.

Use `haveI : Fintype (K ⧸ S) := Fintype.ofFinite _`. Use `⟨Finset.univ.image (fun q : K ⧸ S => q.out), ?_, ?_⟩` and prove the remaining obligations. Conclude with `⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ((1 : K) : K ⧸ S))⟩`. Introduce `V' _ _ ρ' v' h'`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Establish `hinj : Function.Injective (fun q : K ⧸ S => q.out)` using `Quotient.out_injective`. Rewrite using `[Finset.sum_image (fun a _ b _ hab => hinj hab)]`. Use `set F : K → V' := fun x => (((χ x)⁻¹ : kˣ) : k) • ρ' x v' with hF`. Establish `hcos : ∀ a b : K, (a : K ⧸ S) = (b : K ⧸ S) → F a = F b`. Introduce `a b hab`.

Take `⟨h1, h2⟩ : a⁻¹ * b ∈ S` from `QuotientGroup.eq.1 hab`. Establish `e : b = a * (a⁻¹ * b)` using `by group`. Generalize the expression as in `a⁻¹ * b = c at h1 h2 e`. Substitute `e` using the available equality. Simplify using `only [hF, map_mul, h2, mul_one, Subgroup.coe_mul, Module.End.mul_apply, h' _ h1]`.

Establish `hmul : ∀ y x : K, ρ' y (F x) = (χ y : k) • F (y * x)`. Introduce `y x`. Simplify using `only [hF, map_smul, map_mul, Subgroup.coe_mul, Module.End.mul_apply, smul_smul]`. Use `congr 1`. Rewrite using `[← Units.val_mul]`.

Use `congr 1`. Rewrite using `[mul_inv, mul_inv_cancel_left]`. Introduce `y`. Use `show ρ' y (∑ q : K ⧸ S, F q.out) = (χ y : k) • ∑ q : K ⧸ S, F q.out`. Rewrite using `[map_sum, Finset.smul_sum]`.

Use `Fintype.sum_equiv (MulAction.toPerm y) _ _ fun q => ?_` and prove the remaining obligations. Rewrite using `[hmul]`. Use `congr 1`. Apply `hcos` to reduce the goal to its premises. Rewrite using `[QuotientGroup.out_eq']`.

Use `show _ = y • q`. Use `conv_rhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.repAvg :
    ∀ {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] [CharZero k] [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation k G V) (K : Subgroup G) (χ : K →* kˣ), IsCompact (K : Set G) → IsOpen {x : K | χ x = 1} → ∀ v : V, IsOpen {g : G | ρ g v = v} → ∃ (s : Finset K), s.Nonempty ∧ ∀ (V' : Type) [AddCommGroup V'] [Module k V'] (ρ' : Representation k G V') (v' : V'), (∀ g, ρ g v = v → ρ' g v' = v') → ((s.card : k)⁻¹ • ∑ x ∈ s, (((χ x)⁻¹ : kˣ) : k) • ρ' x v') ∈ eig ρ' K χ := by
  intro k G V _ _ _ _ _ _ _ ρ K χ hK hχ v hv
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let S : Subgroup K :=
    { carrier := {x | ρ (x : G) v = v ∧ χ x = 1}
      mul_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨?_, by rw [map_mul, hx', hy', mul_one]⟩
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
      one_mem' := ⟨by simp, map_one χ⟩
      inv_mem' := by
        rintro x ⟨hx, hx'⟩
        refine ⟨?_, by rw [map_inv, hx', inv_one]⟩
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hSo : IsOpen (S : Set K) := (hv.preimage continuous_subtype_val).inter hχ
  haveI : Finite (K ⧸ S) := S.quotient_finite_of_isOpen hSo
  haveI : Fintype (K ⧸ S) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : K ⧸ S => q.out), ?_, ?_⟩
  · exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ((1 : K) : K ⧸ S))⟩
  intro V' _ _ ρ' v' h'
  refine Submodule.smul_mem _ _ ?_
  have hinj : Function.Injective (fun q : K ⧸ S => q.out) := Quotient.out_injective
  rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
  set F : K → V' := fun x => (((χ x)⁻¹ : kˣ) : k) • ρ' x v' with hF
  have hcos : ∀ a b : K, (a : K ⧸ S) = (b : K ⧸ S) → F a = F b := by
    intro a b hab
    obtain ⟨h1, h2⟩ : a⁻¹ * b ∈ S := QuotientGroup.eq.1 hab
    have e : b = a * (a⁻¹ * b) := by group
    generalize a⁻¹ * b = c at h1 h2 e
    subst e
    simp only [hF, map_mul, h2, mul_one, Subgroup.coe_mul, Module.End.mul_apply, h' _ h1]
  have hmul : ∀ y x : K, ρ' y (F x) = (χ y : k) • F (y * x) := by
    intro y x
    simp only [hF, map_smul, map_mul, Subgroup.coe_mul, Module.End.mul_apply, smul_smul]
    congr 1
    rw [← Units.val_mul]
    congr 1
    rw [mul_inv, mul_inv_cancel_left]
  intro y
  show ρ' y (∑ q : K ⧸ S, F q.out) = (χ y : k) • ∑ q : K ⧸ S, F q.out
  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (MulAction.toPerm y) _ _ fun q => ?_
  rw [hmul]
  congr 1
  apply hcos
  rw [QuotientGroup.out_eq']
  show _ = y • q
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rfl
