import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockParOpp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPartMul
open MeasureTheory Matrix
open scoped Classical

namespace GlobalTheory.CentSep

/- English proof (translation)
Use `⟨b.repr (g (b k)) k, ?_⟩` and prove the remaining obligations. Use `set x := g (b k) with hx`. Establish `hfx : f x = μ k • x`. Use `congrArg (fun φ : Module.End L V => φ (b k)) hg` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, hf] at this`.

Rewrite using `[hx, ← this, map_smul]`. Establish `hrep : ∀ y : V, ∀ j, b.repr (f y) j = μ j * b.repr y j`. Introduce `y j`. Establish `key : (b.coord j).comp f = μ j • b.coord j`. Use `b.ext fun i => ?_` and prove the remaining obligations.

Simplify using `only [LinearMap.comp_apply, hf, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, LinearMap.smul_apply, smul_eq_mul, Finsupp.single_apply]`. Use `split_ifs with h`. Substitute `h` using the available equality. Both sides reduce to the same expression. Simplify using the standard rewrite rules.

Conclude with `congrArg (fun φ : V →ₗ[L] L => φ y) key`. Apply `b.ext_elem` to reduce the goal to its premises. Introduce `j`. Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality.

Simplify using the standard rewrite rules. Establish `h1` using `hrep x j`. Rewrite `h1` using `[hfx, map_smul, Finsupp.smul_apply, smul_eq_mul]`. Establish `h0 : b.repr x j = 0`. Establish `h2 : (μ j - μ k) * b.repr x j = 0` using `by linear_combination -h1`.

Break down `mul_eq_zero.mp h2 with h | h` into its components or cases. Conclude with `absurd (hμ (sub_eq_zero.mp h)) hj`. Conclude with `h`. Rewrite using `[h0, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hj), smul_zero]`.
-/
theorem apply_basis_eq_smul {L V κ : Type} [Field L] [AddCommGroup V] [Module L V]
    (b : Module.Basis κ L V) (μ : κ → L) (hμ : Function.Injective μ)
    (f g : Module.End L V) (hf : ∀ k, f (b k) = μ k • b k) (hg : g ∘ₗ f = f ∘ₗ g) (k : κ) :
    ∃ c : L, g (b k) = c • b k := by
  refine ⟨b.repr (g (b k)) k, ?_⟩
  set x := g (b k) with hx
  have hfx : f x = μ k • x := by
    have := congrArg (fun φ : Module.End L V => φ (b k)) hg
    simp only [LinearMap.comp_apply, hf] at this
    rw [hx, ← this, map_smul]
  have hrep : ∀ y : V, ∀ j, b.repr (f y) j = μ j * b.repr y j := by
    intro y j
    have key : (b.coord j).comp f = μ j • b.coord j := by
      refine b.ext fun i => ?_
      simp only [LinearMap.comp_apply, hf, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
        LinearMap.smul_apply, smul_eq_mul, Finsupp.single_apply]
      split_ifs with h
      · subst h; rfl
      · simp
    exact congrArg (fun φ : V →ₗ[L] L => φ y) key
  apply b.ext_elem
  intro j
  by_cases hj : j = k
  · subst hj; simp
  · have h1 := hrep x j
    rw [hfx, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    have h0 : b.repr x j = 0 := by
      have h2 : (μ j - μ k) * b.repr x j = 0 := by linear_combination -h1
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd (hμ (sub_eq_zero.mp h)) hj
      · exact h
    rw [h0, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hj),
      smul_zero]

/- English proof (translation)
Use `b.ext fun k => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `apply_basis_eq_smul b μ hμ f g hf hg k`. Take `⟨d, hd⟩` from `apply_basis_eq_smul b μ hμ f h hf hh k`. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[hd, map_smul, hc, map_smul, hd, smul_smul, smul_smul, mul_comm]`.
-/
theorem comm_of_eigenbasis {L V κ : Type} [Field L] [AddCommGroup V] [Module L V]
    (b : Module.Basis κ L V) (μ : κ → L) (hμ : Function.Injective μ)
    (f g h : Module.End L V) (hf : ∀ k, f (b k) = μ k • b k) (hg : g ∘ₗ f = f ∘ₗ g)
    (hh : h ∘ₗ f = f ∘ₗ h) : g ∘ₗ h = h ∘ₗ g := by
  refine b.ext fun k => ?_
  obtain ⟨c, hc⟩ := apply_basis_eq_smul b μ hμ f g hf hg k
  obtain ⟨d, hd⟩ := apply_basis_eq_smul b μ hμ f h hf hh k
  simp only [LinearMap.comp_apply]
  rw [hd, map_smul, hc, map_smul, hd, smul_smul, smul_smul, mul_comm]

/- English proof (translation)
Break down `isEmpty_or_nonempty ι with hι | hι` into its components or cases. Conclude with `Subsingleton.elim _ _`. Use `set f := Matrix.toLin' A with hfdef`. Use `set s : Finset L := A.charpoly.roots.toFinset with hsdef`. Establish `hcard : s.card = Fintype.card ι`.

Rewrite using `[hsdef, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs), IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]`. Establish `hev : ∀ μ : (s : Set L), Module.End.HasEigenvalue f μ`. Introduce `μ`. Rewrite using `[Module.End.hasEigenvalue_iff_isRoot_charpoly, hfdef, Matrix.charpoly_toLin']`. Establish `hμ` using `μ.2`.

Simplify using `only [Finset.mem_coe, hsdef, Multiset.mem_toFinset] at hμ`. Conclude with `Polynomial.isRoot_of_mem_roots hμ`. Use `choose v hv using fun μ : (s : Set L) => (hev μ).exists_hasEigenvector`. Establish `hli` using `Module.End.eigenvectors_linearIndependent f (s : Set L) v hv`. Establish `hc : Fintype.card (s : Set L) = Module.finrank L (ι → L)`.

Simplify using `[hcard]`. Use `haveI : Nonempty (s : Set L) := by`. Rewrite using `[← Fintype.card_pos_iff, hc, Module.finrank_fintype_fun_eq_card]`. Conclude with `Fintype.card_pos`. Set `b` to `basisOfLinearIndependentOfCardEqFinrank hli hc`.

Establish `hb : ∀ k, f (b k) = (k : L) • b k` using `fun k => by`. Simplify using `only [b, coe_basisOfLinearIndependentOfCardEqFinrank]`. Conclude with `(hv k).apply_eq_smul`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Rewrite using `[Matrix.toLin'_mul, Matrix.toLin'_mul]`.

Conclude with `comm_of_eigenbasis b (fun k => (k : L)) Subtype.coe_injective f _ _ hb (by rw [← Matrix.toLin'_mul, hG, Matrix.toLin'_mul]) (by rw [← Matrix.toLin'_mul, hH, Matrix.toLin'_mul])`.
-/
theorem comm_of_separable_algClosed {L ι : Type} [Field L] [IsAlgClosed L] [Fintype ι] [DecidableEq ι]
    (A G H : Matrix ι ι L) (hs : A.charpoly.Separable) (hG : G * A = A * G) (hH : H * A = A * H) :
    G * H = H * G := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Subsingleton.elim _ _
  set f := Matrix.toLin' A with hfdef
  set s : Finset L := A.charpoly.roots.toFinset with hsdef
  have hcard : s.card = Fintype.card ι := by
    rw [hsdef, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs),
      IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]
  have hev : ∀ μ : (s : Set L), Module.End.HasEigenvalue f μ := by
    intro μ
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hfdef, Matrix.charpoly_toLin']
    have hμ := μ.2
    simp only [Finset.mem_coe, hsdef, Multiset.mem_toFinset] at hμ
    exact Polynomial.isRoot_of_mem_roots hμ
  choose v hv using fun μ : (s : Set L) => (hev μ).exists_hasEigenvector
  have hli := Module.End.eigenvectors_linearIndependent f (s : Set L) v hv
  have hc : Fintype.card (s : Set L) = Module.finrank L (ι → L) := by
    simp [hcard]
  haveI : Nonempty (s : Set L) := by
    rw [← Fintype.card_pos_iff, hc, Module.finrank_fintype_fun_eq_card]; exact Fintype.card_pos
  let b := basisOfLinearIndependentOfCardEqFinrank hli hc
  have hb : ∀ k, f (b k) = (k : L) • b k := fun k => by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank]
    exact (hv k).apply_eq_smul
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  exact comm_of_eigenbasis b (fun k => (k : L)) Subtype.coe_injective f _ _ hb
    (by rw [← Matrix.toLin'_mul, hG, Matrix.toLin'_mul])
    (by rw [← Matrix.toLin'_mul, hH, Matrix.toLin'_mul])

/- English proof (translation)
Introduce `K _ ι _ _ γ g h hs hg hh`. Apply `Units.ext` to reduce the goal to its premises. Establish `hg'` using `congrArg Units.val hg`. Establish `hh'` using `congrArg Units.val hh`. Simplify using `only [Units.val_mul] at hg' hh' ⊢`.

Set `φ` to `algebraMap K (AlgebraicClosure K)`. Apply `Matrix.map_injective φ.injective` to reduce the goal to its premises. Simplify using `only [Matrix.map_mul]`. Apply `comm_of_separable_algClosed ((γ : Matrix ι ι K).map φ)` to reduce the goal to its premises. Rewrite using `[Matrix.charpoly_map]`.

Conclude with `hs.map`. Rewrite using `[← Matrix.map_mul, hg', Matrix.map_mul]`. Rewrite using `[← Matrix.map_mul, hh', Matrix.map_mul]`.
-/
theorem centraliser_comm_of_separable : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (γ g h : GL ι K),
  (γ : Matrix ι ι K).charpoly.Separable → g * γ = γ * g → h * γ = γ * h → g * h = h * g := by
  intro K _ ι _ _ γ g h hs hg hh
  apply Units.ext
  have hg' := congrArg Units.val hg
  have hh' := congrArg Units.val hh
  simp only [Units.val_mul] at hg' hh' ⊢
  let φ := algebraMap K (AlgebraicClosure K)
  apply Matrix.map_injective φ.injective
  simp only [Matrix.map_mul]
  apply comm_of_separable_algClosed ((γ : Matrix ι ι K).map φ)
  · rw [Matrix.charpoly_map]; exact hs.map
  · rw [← Matrix.map_mul, hg', Matrix.map_mul]
  · rw [← Matrix.map_mul, hh', Matrix.map_mul]

end GlobalTheory.CentSep
