import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeContractingHomotopy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwOCommDStatement
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section

namespace GlobalTheory.EZ

/- English proof (translation)
Use extensionality with `j`. Simplify using `[fc, clampHom, faceFun, SimplexCategory.δ, Fin.succAbove, Fin.lt_def]`. Apply the tactic sequence `split_ifs <;> simp_all <;> omega`.
-/
theorem fc_succ_eq_δ (n i : ℕ) (hi : i < n + 2) :
    fc (n + 1) n i = SimplexCategory.δ (⟨i, hi⟩ : Fin (n + 2)) := by
  ext j
  simp [fc, clampHom, faceFun, SimplexCategory.δ, Fin.succAbove, Fin.lt_def]
  split_ifs <;> simp_all <;> omega

def diagOp : SimplicialObject BOp := Functor.diag SimplexCategoryᵒᵖ ⋙ Free.embedding ℤ _

/- English proof (translation)
Rewrite using `[dD, if_pos rfl, AlternatingFaceMapComplex.objD, ← Fin.sum_univ_eq_sum_range]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[fc_succ_eq_δ n i i.2]`. Both sides reduce to the same expression.
-/
theorem dD_succ_eq_objD (n : ℕ) : dD (n + 1) n = AlternatingFaceMapComplex.objD diagOp n := by
  rw [dD, if_pos rfl, AlternatingFaceMapComplex.objD, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fc_succ_eq_δ n i i.2]
  rfl

/- English proof (translation)
Distinguish the cases in `h1 : n = m + 1`. Substitute `h1` using the available equality. Distinguish the cases in `h2 : m = k + 1`. Substitute `h2` using the available equality. Rewrite using `[dD_succ_eq_objD, dD_succ_eq_objD]`.

Conclude with `AlternatingFaceMapComplex.d_squared diagOp k`. Rewrite using `[show dD m k = 0 from if_neg h2, Limits.comp_zero]`. Rewrite using `[show dD n m = 0 from if_neg h1, Limits.zero_comp]`.
-/
theorem dD_comp_dD (n m k : ℕ) : dD n m ≫ dD m k = 0 := by
  by_cases h1 : n = m + 1
  · subst h1
    by_cases h2 : m = k + 1
    · subst h2
      rw [dD_succ_eq_objD, dD_succ_eq_objD]
      exact AlternatingFaceMapComplex.d_squared diagOp k
    · rw [show dD m k = 0 from if_neg h2, Limits.comp_zero]
  · rw [show dD n m = 0 from if_neg h1, Limits.zero_comp]

/- English proof (translation)
Rewrite using `[awO, if_pos rfl]`. Establish `h1 : idc 0 0 = 𝟙 _` using `Subsingleton.elim _ _`. Establish `h2 : backc 0 0 0 = 𝟙 _` using `Subsingleton.elim _ _`. Rewrite using `[h1, h2]`. Both sides reduce to the same expression.
-/
theorem awO_zero : awO 0 0 0 = 𝟙 (bo 0 0) := by
  rw [awO, if_pos rfl]
  have h1 : idc 0 0 = 𝟙 _ := Subsingleton.elim _ _
  have h2 : backc 0 0 0 = 𝟙 _ := Subsingleton.elim _ _
  rw [h1, h2]
  rfl

def awThen (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (n : ℕ) : bo n n ⟶ bo n n :=
  ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n

def awHtpy (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1))) :
    ∀ n : ℕ, bo n n ⟶ bo (n + 1) (n + 1) := fun n =>
  Nat.rec (motive := fun n => bo n n ⟶ bo (n + 1) (n + 1)) 0
    (fun k K => cone (k + 1) (k + 1) (k + 1) (awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ K)) n

/- English proof (translation)
Simplify using `only [awThen, Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]`. Establish `e1 : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ G x.1 x.2 (n + 1) ≫ dD (n + 1) n = ∑ y ∈ Finset.HasAntidiagonal.antidiagonal n, awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 y.1 y.2 ≫ G y.1 y.2 n` using `fun x hx => by rw [hG _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.mp hx), Preadditive.comp_sum]`. Establish `e2 : ∀ y ∈ Finset.HasAntidiagonal.antidiagonal n, dD (n + 1) n ≫ awO n y.1 y.2 ≫ G y.1 y.2 n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 y.1 y.2 ≫ G y.1 y.2 n` using `fun y hy => by`. Rewrite using `[← Category.assoc, haw _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.mp hy), Preadditive.sum_comp]`. Simplify using `only [Category.assoc]`.

Rewrite using `[Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_comm]`.
-/
theorem awThen_comm (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n)
    (haw : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b) (n : ℕ) :
    awThen G (n + 1) ≫ dD (n + 1) n = dD (n + 1) n ≫ awThen G n := by
  simp only [awThen, Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  have e1 : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1),
      awO (n + 1) x.1 x.2 ≫ G x.1 x.2 (n + 1) ≫ dD (n + 1) n =
        ∑ y ∈ Finset.HasAntidiagonal.antidiagonal n, awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 y.1 y.2 ≫ G y.1 y.2 n :=
    fun x hx => by rw [hG _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.mp hx), Preadditive.comp_sum]
  have e2 : ∀ y ∈ Finset.HasAntidiagonal.antidiagonal n,
      dD (n + 1) n ≫ awO n y.1 y.2 ≫ G y.1 y.2 n =
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 y.1 y.2 ≫ G y.1 y.2 n :=
    fun y hy => by
      rw [← Category.assoc, haw _ _ _ (Finset.HasAntidiagonal.mem_antidiagonal.mp hy), Preadditive.sum_comp]
      simp only [Category.assoc]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_comm]

/- English proof (translation)
Establish `h0 : awThen G 0 = 𝟙 _`. Simplify using `[awThen, awO_zero, hG0]`. Establish `key : ∀ k : ℕ, (awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ awHtpy G cone k) ≫ dD (k + 1) k = 0 → awThen G (k + 1) = 𝟙 _ + awHtpy G cone (k + 1) ≫ dD (k + 1 + 1) (k + 1) + dD (k + 1) k ≫ awHtpy G cone k`. Introduce `k hk`. Establish `h` using `hcone (k + 1) (k + 1) k (awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ awHtpy G cone k)`.

Rewrite `h` using `[hk, map_zero, sub_zero]`. Establish `h' : awHtpy G cone (k + 1) ≫ dD (k + 1 + 1) (k + 1) = awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ awHtpy G cone k` using `h`. Rewrite using `[h']`. Normalize the expressions using the abelian group laws. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Apply `key` to reduce the goal to its premises. Establish `hK : awHtpy G cone 0 = 0` using `rfl`. Rewrite using `[hK, Preadditive.sub_comp, Preadditive.sub_comp, awThen_comm G hG haw 0, h0]`.

Simplify using the standard rewrite rules. Consider the case `succ j ih`. Apply `key` to reduce the goal to its premises. Rewrite using `[Preadditive.sub_comp, Preadditive.sub_comp, awThen_comm G hG haw (j + 1), ih, Preadditive.comp_add, Preadditive.comp_add, ← Category.assoc (dD (j + 1 + 1) (j + 1)) (dD (j + 1) j), dD_comp_dD, Limits.zero_comp]`. Simplify using `only [Category.comp_id, Category.id_comp, Category.assoc, add_zero]`.

Normalize the expressions using the abelian group laws.
-/
theorem awHtpy_spec (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (hG0 : G 0 0 0 = 𝟙 (bo 0 0))
    (hG : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n)
    (haw : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b)
    (cone : ∀ a b n : ℕ, (bo a b ⟶ bo n n) →+ (bo a b ⟶ bo (n + 1) (n + 1)))
    (hcone : ∀ (a b n : ℕ) (r : bo a b ⟶ bo (n + 1) (n + 1)),
      cone a b (n + 1) r ≫ dD (n + 2) (n + 1) = r - cone a b n (r ≫ dD (n + 1) n)) :
    ∀ n : ℕ, awThen G (n + 1) = 𝟙 _ + awHtpy G cone (n + 1) ≫ dD (n + 1 + 1) (n + 1) +
      dD (n + 1) n ≫ awHtpy G cone n := by
  have h0 : awThen G 0 = 𝟙 _ := by
    simp [awThen, awO_zero, hG0]
  have key : ∀ k : ℕ,
      (awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ awHtpy G cone k) ≫ dD (k + 1) k = 0 →
      awThen G (k + 1) = 𝟙 _ + awHtpy G cone (k + 1) ≫ dD (k + 1 + 1) (k + 1) +
        dD (k + 1) k ≫ awHtpy G cone k := by
    intro k hk
    have h := hcone (k + 1) (k + 1) k (awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ awHtpy G cone k)
    rw [hk, map_zero, sub_zero] at h
    have h' : awHtpy G cone (k + 1) ≫ dD (k + 1 + 1) (k + 1) =
        awThen G (k + 1) - 𝟙 _ - dD (k + 1) k ≫ awHtpy G cone k := h
    rw [h']
    abel
  intro n
  induction n with
  | zero =>
    apply key
    have hK : awHtpy G cone 0 = 0 := rfl
    rw [hK, Preadditive.sub_comp, Preadditive.sub_comp, awThen_comm G hG haw 0, h0]
    simp
  | succ j ih =>
    apply key
    rw [Preadditive.sub_comp, Preadditive.sub_comp, awThen_comm G hG haw (j + 1), ih,
      Preadditive.comp_add, Preadditive.comp_add, ← Category.assoc (dD (j + 1 + 1) (j + 1)) (dD (j + 1) j),
      dD_comp_dD, Limits.zero_comp]
    simp only [Category.comp_id, Category.id_comp, Category.assoc, add_zero]
    abel

/- English proof (translation)
Introduce `G hG0 hG`. Take `⟨cone, ε, -, -, hcone⟩` from `GlobalTheory.T.cone_contracting_homotopy`. Establish `haw` using `GlobalTheory.T.dD_comp_awO_eq_sum_awO_comp_dT`. Use `⟨fun n m => if h : m = n + 1 then awHtpy G cone n ≫ eqToHom (by rw [h]) else 0, fun n => ?_⟩` and prove the remaining obligations. Consider the cases of `n with`.

Consider the case `zero`. Establish `h0 : awThen G 0 = 𝟙 _`. Simplify using `[awThen, awO_zero, hG0]`. Establish `hK : awHtpy G cone 0 = 0` using `rfl`. Express the relevant statement in the definitionally equal form `awThen G 0 = _`.

Simplify using `[h0, hK, dD]`. Consider the case `succ k`. Express the relevant statement in the definitionally equal form `awThen G (k + 1) = _`. Simplify using `only [dif_pos, eqToHom_refl, Category.comp_id, Nat.add_sub_cancel]`. Conclude with `awHtpy_spec G hG0 hG haw cone hcone k`.
-/
theorem awThen_homotopic : ∀ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) →
    (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) →
    ∃ H : ∀ n m : ℕ, bo n n ⟶ bo m m, ∀ n : ℕ,
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, awO n x.1 x.2 ≫ G x.1 x.2 n =
        𝟙 (bo n n) + H n (n + 1) ≫ dD (n + 1) n + dD n (n - 1) ≫ H (n - 1) n := by
  intro G hG0 hG
  obtain ⟨cone, ε, -, -, hcone⟩ := GlobalTheory.T.cone_contracting_homotopy
  have haw := GlobalTheory.T.dD_comp_awO_eq_sum_awO_comp_dT
  refine ⟨fun n m => if h : m = n + 1 then awHtpy G cone n ≫ eqToHom (by rw [h]) else 0, fun n => ?_⟩
  cases n with
  | zero =>
    have h0 : awThen G 0 = 𝟙 _ := by
      simp [awThen, awO_zero, hG0]
    have hK : awHtpy G cone 0 = 0 := rfl
    change awThen G 0 = _
    simp [h0, hK, dD]
  | succ k =>
    change awThen G (k + 1) = _
    simp only [dif_pos, eqToHom_refl, Category.comp_id, Nat.add_sub_cancel]
    exact awHtpy_spec G hG0 hG haw cone hcone k

end GlobalTheory.EZ
