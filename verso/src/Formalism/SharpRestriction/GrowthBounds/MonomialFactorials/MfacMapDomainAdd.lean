import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PhisBRenameMul
import Formalism.MahlerMeasure.MahlerMeasureProofs.RemoveS

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

section Disj

variable {k σ τ : Type} [Field k] [DecidableEq σ] [DecidableEq τ]

/- English proof (translation)
Establish `ha : a = b`. Use extensionality with `x`. Establish `h1` using `DFunLike.congr_fun h (e x)`. Simplify `h1` using `[Finsupp.mapDomain_apply he, hβ, hβ']`. Substitute `ha` using the available equality.

Conclude with `⟨rfl, add_left_cancel h⟩`.
-/
theorem mapDomain_add_inj (e : τ → σ) (he : Function.Injective e) (a b : τ →₀ ℕ) (β β' : σ →₀ ℕ)
    (hβ : ∀ x, β (e x) = 0) (hβ' : ∀ x, β' (e x) = 0)
    (h : Finsupp.mapDomain e a + β = Finsupp.mapDomain e b + β') : a = b ∧ β = β' := by
  have ha : a = b := by
    ext x
    have h1 := DFunLike.congr_fun h (e x)
    simpa [Finsupp.mapDomain_apply he, hβ, hβ'] using h1
  subst ha
  exact ⟨rfl, add_left_cancel h⟩

/- English proof (translation)
Unfold `mfac`. Establish `hd : Disjoint (Finsupp.mapDomain e a).support β.support`. Rewrite using `[Finset.disjoint_left]`. Introduce `x hx hx'`. Take `⟨y, _, rfl⟩` from `Finset.mem_image.1 (Finsupp.mapDomain_support hx)`.

Conclude with `(Finsupp.mem_support_iff.1 hx') (hβ y)`. Rewrite using `[Finsupp.prod_add_index_of_disjoint hd, Finsupp.prod_mapDomain_index_inj he]`.
-/
theorem mfac_mapDomain_add (e : τ → σ) (he : Function.Injective e) (a : τ →₀ ℕ) (β : σ →₀ ℕ)
    (hβ : ∀ x, β (e x) = 0) : (mfac (Finsupp.mapDomain e a + β) : k) = mfac a * mfac β := by
  unfold mfac
  have hd : Disjoint (Finsupp.mapDomain e a).support β.support := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
    exact (Finsupp.mem_support_iff.1 hx') (hβ y)
  rw [Finsupp.prod_add_index_of_disjoint hd, Finsupp.prod_mapDomain_index_inj he]

/- English proof (translation)
Use `set F := rename e A * monomial β (1 : k) with hF`. Use `set G := rename e B * monomial β' c with hG`. Establish `hcF : ∀ m, F.coeff (Finsupp.mapDomain e m + β) = A.coeff m`. Introduce `m`. Rewrite using `[hF, MvPolynomial.coeff_mul_monomial, MvPolynomial.coeff_rename_mapDomain e he, mul_one]`.

Establish `hcF0 : ∀ n, F.coeff n ≠ 0 → ∃ m, n = Finsupp.mapDomain e m + β ∧ A.coeff m ≠ 0`. Introduce `n hn`. Rewrite `hn` using `[hF, MvPolynomial.coeff_mul_monomial']`. Use `split_ifs at hn with hle`. Rewrite `hn` using `[mul_one]`.

Take `⟨u, hu, hu0⟩` from `MvPolynomial.coeff_rename_ne_zero e A (n - β) hn`. Use `⟨u, ?_, hu0⟩` and prove the remaining obligations. Rewrite using `[hu]`. Conclude with `(tsub_add_cancel_of_le hle).symm`. Conclude with `absurd rfl hn`.

Establish `hcG : ∀ m, G.coeff (Finsupp.mapDomain e m + β) = if β = β' then B.coeff m * c else 0`. Introduce `m`. Use `split_ifs with hb`. Substitute `hb` using the available equality. Rewrite using `[hG, MvPolynomial.coeff_mul_monomial, MvPolynomial.coeff_rename_mapDomain e he]`.

Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[hG, MvPolynomial.coeff_mul_monomial']`. Use `split_ifs at hne with hle`. Establish `h1 : (rename e B).coeff (Finsupp.mapDomain e m + β - β') ≠ 0` using `fun h0 => hne (by rw [h0, zero_mul])`. Take `⟨u, hu, -⟩` from `MvPolynomial.coeff_rename_ne_zero e B _ h1`.

Establish `h2 : Finsupp.mapDomain e m + β = Finsupp.mapDomain e u + β'`. Rewrite using `[hu]`. Conclude with `(tsub_add_cancel_of_le hle).symm`. Conclude with `hb (mapDomain_add_inj e he m u β β' hβ hβ' h2).2`. Conclude with `hne rfl`.

Establish `hmf : ∀ m : τ →₀ ℕ, ((Finsupp.mapDomain e m + β).prod fun _ j => (j.factorial : k)) = (m.prod fun _ j => (j.factorial : k)) * (β.prod fun _ j => (j.factorial : k))` using `fun m => mfac_mapDomain_add e he m β hβ`. Unfold `Formalism.GM.M.fockK`. Establish `hsub : F.support ⊆ A.support.image (fun m => Finsupp.mapDomain e m + β)`. Introduce `n hn`. Take `⟨m, rfl, hm⟩` from `hcF0 n (MvPolynomial.mem_support_iff.1 hn)`.

Conclude with `Finset.mem_image.2 ⟨m, MvPolynomial.mem_support_iff.2 hm, rfl⟩`. Rewrite using `[Finset.sum_subset hsub (fun n _ hn => by`. Rewrite `hn` using `[MvPolynomial.mem_support_iff, not_not]`. Rewrite using `[hn]`. Use the proof step `ring)]`.

Establish `hinj : Set.InjOn (fun m => Finsupp.mapDomain e m + β) A.support` using `fun a _ b _ hab => (mapDomain_add_inj e he a b β β hβ hβ hab).1`. Rewrite using `[Finset.sum_image hinj]`. Simplify using `only [hcF, hcG, hmf]`. Use `split_ifs with hb`. Rewrite using `[Finset.mul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `x _`. Unfold `mfac`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem fockK_rename_mul (e : τ → σ) (he : Function.Injective e) (A B : MvPolynomial τ k) (β β' : σ →₀ ℕ) (c : k)
    (hβ : ∀ x, β (e x) = 0) (hβ' : ∀ x, β' (e x) = 0) :
    Formalism.GM.M.fockK (rename e A * monomial β 1) (rename e B * monomial β' c) =
      if β = β' then c * mfac β * Formalism.GM.M.fockK A B else 0 := by
  classical
  set F := rename e A * monomial β (1 : k) with hF
  set G := rename e B * monomial β' c with hG
  have hcF : ∀ m, F.coeff (Finsupp.mapDomain e m + β) = A.coeff m := by
    intro m
    rw [hF, MvPolynomial.coeff_mul_monomial, MvPolynomial.coeff_rename_mapDomain e he, mul_one]
  have hcF0 : ∀ n, F.coeff n ≠ 0 → ∃ m, n = Finsupp.mapDomain e m + β ∧ A.coeff m ≠ 0 := by
    intro n hn
    rw [hF, MvPolynomial.coeff_mul_monomial'] at hn
    split_ifs at hn with hle
    · rw [mul_one] at hn
      obtain ⟨u, hu, hu0⟩ := MvPolynomial.coeff_rename_ne_zero e A (n - β) hn
      refine ⟨u, ?_, hu0⟩
      rw [hu]
      exact (tsub_add_cancel_of_le hle).symm
    · exact absurd rfl hn
  have hcG : ∀ m, G.coeff (Finsupp.mapDomain e m + β) = if β = β' then B.coeff m * c else 0 := by
    intro m
    split_ifs with hb
    · subst hb
      rw [hG, MvPolynomial.coeff_mul_monomial, MvPolynomial.coeff_rename_mapDomain e he]
    · by_contra hne
      rw [hG, MvPolynomial.coeff_mul_monomial'] at hne
      split_ifs at hne with hle
      · have h1 : (rename e B).coeff (Finsupp.mapDomain e m + β - β') ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
        obtain ⟨u, hu, -⟩ := MvPolynomial.coeff_rename_ne_zero e B _ h1
        have h2 : Finsupp.mapDomain e m + β = Finsupp.mapDomain e u + β' := by
          rw [hu]
          exact (tsub_add_cancel_of_le hle).symm
        exact hb (mapDomain_add_inj e he m u β β' hβ hβ' h2).2
      · exact hne rfl
  have hmf : ∀ m : τ →₀ ℕ, ((Finsupp.mapDomain e m + β).prod fun _ j => (j.factorial : k)) =
      (m.prod fun _ j => (j.factorial : k)) * (β.prod fun _ j => (j.factorial : k)) :=
    fun m => mfac_mapDomain_add e he m β hβ
  unfold Formalism.GM.M.fockK
  have hsub : F.support ⊆ A.support.image (fun m => Finsupp.mapDomain e m + β) := by
    intro n hn
    obtain ⟨m, rfl, hm⟩ := hcF0 n (MvPolynomial.mem_support_iff.1 hn)
    exact Finset.mem_image.2 ⟨m, MvPolynomial.mem_support_iff.2 hm, rfl⟩
  rw [Finset.sum_subset hsub (fun n _ hn => by
    rw [MvPolynomial.mem_support_iff, not_not] at hn
    rw [hn]
    ring)]
  have hinj : Set.InjOn (fun m => Finsupp.mapDomain e m + β) A.support :=
    fun a _ b _ hab => (mapDomain_add_inj e he a b β β hβ hβ hab).1
  rw [Finset.sum_image hinj]
  simp only [hcF, hcG, hmf]
  split_ifs with hb
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    unfold mfac
    ring
  · simp

end Disj

end Formalism.MainNotions.G.SymmetricFormBlocks

end
