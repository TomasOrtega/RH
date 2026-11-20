import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Dblock

/- English proof (translation)
Introduce `R _ _ _ r N _ _ K _ _ I hI w hw k`. Set `I' : Submodule R K` to `{ carrier := {x | ∃ a : R, a ≠ 0 ∧ a • x ∈ I} zero_mem' := ⟨1, one_ne_zero, by simp⟩ add_mem' := by`. Introduce and unpack `x y ⟨a, ha, hax⟩ ⟨b, hb, hby⟩`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`.

Use `I.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `I.smul_mem _ hax`. Rewrite using `[mul_smul]`. Conclude with `I.smul_mem _ hby`.

Use the proof step `smul_mem' := by`. Introduce and unpack `c x ⟨a, ha, hax⟩`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_comm]`. Conclude with `I.smul_mem _ hax }`.

Establish `hle : I ≤ I'` using `fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩`. Establish `hflat : Module.Flat R (K ⧸ I')`. Rewrite using `[Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]`. Introduce `y hy`. Take `⟨x, rfl⟩` from `I'.mkQ_surjective y`.

Take `⟨a, ha⟩` from `(Submodule.mem_torsion_iff _).1 hy`. Establish `hax : (a : R) • x ∈ I'`. Rewrite using `[← Submodule.Quotient.mk_eq_zero]`. Simplify `ha` using `[Submonoid.smul_def]`. Take `⟨b, hb, hbx⟩` from `hax`.

Establish `hx : x ∈ I'` using `⟨b * a, mul_ne_zero hb (nonZeroDivisors.ne_zero a.2), by`. Rewrite using `[mul_smul]`. Conclude with `hbx⟩`. Simplify using `using (Submodule.Quotient.mk_eq_zero I').2 hx`. Establish `hinj : Function.Injective (I'.subtype.lTensor N)` using `LinearMap.lTensor_injective_of_exact_of_flat I'.mkQ I'.mkQ_surjective I'.subtype I'.injective_subtype (LinearMap.exact_subtype_mkQ I') N`.

Set `ι : I →ₗ[R] I'` to `Submodule.inclusion hle`. Set `φ : I' →ₗ[R] I` to `LinearMap.codRestrict I (r k • I'.subtype) (fun x => by`. Take `⟨a, ha, hax⟩` from `x.2`. Conclude with `hI a x ha hax k)`. Establish `h1 : ι.lTensor N w = 0`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]`. Conclude with `hw`. Establish `hcomp : φ ∘ₗ ι = r k • LinearMap.id`. Use extensionality with `x`.

Both sides reduce to the same expression. Establish `h2 : φ.lTensor N (ι.lTensor N w) = r k • w`. Rewrite using `[← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomp, LinearMap.lTensor_smul, LinearMap.lTensor_id]`. Both sides reduce to the same expression. Rewrite using `[← h2, h1, map_zero]`.
-/
theorem smul_eq_zero_of_lTensor_subtype_eq_zero :
    ∀ (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (r : ℕ → R) (N : Type)
      [AddCommGroup N] [Module R N] (K : Type) [AddCommGroup K] [Module R K] (I : Submodule R K),
      (∀ (a : R) (x : K), a ≠ 0 → a • x ∈ I → ∀ k, r k • x ∈ I) →
      ∀ w : N ⊗[R] I, I.subtype.lTensor N w = 0 → ∀ k, r k • w = 0 := by
  intro R _ _ _ r N _ _ K _ _ I hI w hw k
  let I' : Submodule R K :=
    { carrier := {x | ∃ a : R, a ≠ 0 ∧ a • x ∈ I}
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro x y ⟨a, ha, hax⟩ ⟨b, hb, hby⟩
        refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
        rw [smul_add]
        refine I.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact I.smul_mem _ hax
        · rw [mul_smul]; exact I.smul_mem _ hby
      smul_mem' := by
        rintro c x ⟨a, ha, hax⟩
        refine ⟨a, ha, ?_⟩
        rw [smul_comm]; exact I.smul_mem _ hax }
  have hle : I ≤ I' := fun x hx => ⟨1, one_ne_zero, by simpa using hx⟩
  have hflat : Module.Flat R (K ⧸ I') := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := I'.mkQ_surjective y
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hy
    have hax : (a : R) • x ∈ I' := by
      rw [← Submodule.Quotient.mk_eq_zero]
      simpa [Submonoid.smul_def] using ha
    obtain ⟨b, hb, hbx⟩ := hax
    have hx : x ∈ I' := ⟨b * a, mul_ne_zero hb (nonZeroDivisors.ne_zero a.2), by
      rw [mul_smul]; exact hbx⟩
    simpa using (Submodule.Quotient.mk_eq_zero I').2 hx
  have hinj : Function.Injective (I'.subtype.lTensor N) :=
    LinearMap.lTensor_injective_of_exact_of_flat I'.mkQ I'.mkQ_surjective I'.subtype
      I'.injective_subtype (LinearMap.exact_subtype_mkQ I') N
  let ι : I →ₗ[R] I' := Submodule.inclusion hle
  let φ : I' →ₗ[R] I := LinearMap.codRestrict I (r k • I'.subtype) (fun x => by
    obtain ⟨a, ha, hax⟩ := x.2
    exact hI a x ha hax k)
  have h1 : ι.lTensor N w = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    exact hw
  have hcomp : φ ∘ₗ ι = r k • LinearMap.id := by
    ext x
    rfl
  have h2 : φ.lTensor N (ι.lTensor N w) = r k • w := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomp, LinearMap.lTensor_smul,
      LinearMap.lTensor_id]
    rfl
  rw [← h2, h1, map_zero]

end GlobalTheory.CompanionTheory.Dblock
