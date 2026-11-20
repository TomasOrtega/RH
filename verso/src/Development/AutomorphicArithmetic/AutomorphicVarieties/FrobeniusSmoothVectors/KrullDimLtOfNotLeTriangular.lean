import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CharpolyCoeffsInSubalgebra
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TameInertiaCondition

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Rewrite using `[ringKrullDim_quotient]`. Use `iSup_le fun s => ?_` and prove the remaining obligations. Use `le_trans ?_ (h s.head.1.asIdeal s.head.1.isPrime s.head.2)` and prove the remaining obligations. Rewrite using `[ringKrullDim_quotient]`. Set `t : LTSeries (PrimeSpectrum.zeroLocus (R` to `A) s.head.1.asIdeal) := ⟨s.length, fun i => ⟨(s i).1, (show s.head.1 ≤ (s i).1 from s.head_le i)⟩, fun i => s.step i⟩`.

Conclude with `Order.LTSeries.length_le_krullDim t`.
-/
private theorem dim_le_of_primes {A : Type} [CommRing A] (I : Ideal A) (c : WithBot ℕ∞)
    (h : ∀ P : Ideal A, P.IsPrime → I ≤ P → ringKrullDim (A ⧸ P) ≤ c) : ringKrullDim (A ⧸ I) ≤ c := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun s => ?_
  refine le_trans ?_ (h s.head.1.asIdeal s.head.1.isPrime s.head.2)
  rw [ringKrullDim_quotient]
  let t : LTSeries (PrimeSpectrum.zeroLocus (R := A) s.head.1.asIdeal) :=
    ⟨s.length, fun i => ⟨(s i).1, (show s.head.1 ≤ (s i).1 from s.head_le i)⟩, fun i => s.step i⟩
  exact Order.LTSeries.length_le_krullDim t

/- English proof (translation)
The claim follows from `ringKrullDim_le_of_surjective (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)`.
-/
private theorem dim_anti {A : Type} [CommRing A] {I J : Ideal A} (h : I ≤ J) :
    ringKrullDim (A ⧸ J) ≤ ringKrullDim (A ⧸ I) :=
  ringKrullDim_le_of_surjective (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)

/- English proof (translation)
Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot => exact bot_le`. Consider the case `coe a`. Proceed by induction on `a using ENat.recTopCoe with`. Consider the case `top`.

It suffices to derive a contradiction. Establish `h' : (⊤ : ℕ∞) + (b : ℕ∞) ≤ (c : ℕ∞)` using `by exact_mod_cast h`. Simplify using `at h'`. Consider the case `coe a`. Establish `h' : a + b ≤ c` using `by exact_mod_cast h`.

Establish `: a ≤ m` using `by omega`. Conclude with `this` after adjusting the coercions.
-/
private theorem le_of_add_le {a : WithBot ℕ∞} {b c m : ℕ} (h : a + b ≤ (c : ℕ)) (hm : c ≤ m + b) :
    a ≤ (m : ℕ) := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : (⊤ : ℕ∞) + (b : ℕ∞) ≤ (c : ℕ∞) := by exact_mod_cast h
      simp at h'
    | coe a =>
      have h' : a + b ≤ c := by exact_mod_cast h
      have : a ≤ m := by omega
      exact_mod_cast this

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ n hF hn S x L hB hx`. Take `⟨h1, h2⟩` from `l51 hF hn S x L hx`. Take `⟨hd, hdv⟩` from `hB`. Establish `hlt : ((n * F.d - 1 : ℕ) : WithBot ℕ∞) < (n * F.d : ℕ)`. Apply the tactic sequence `have : n * F.d - 1 < n * F.d := by rcases hn with rfl | rfl <;> omega`.

Conclude with `this` after adjusting the coercions. Establish `hT : ringKrullDim (L.R ⧸ L.ρ.triM) ≤ (n * F.d - 1 : ℕ)`. Use `h1.trans ?_` and prove the remaining obligations. Apply the tactic sequence `have : (n - 1) * F.d + 2 + (3 * C₀ + 5) ≤ n * F.d - 1 := by rcases hn with rfl | rfl <;> omega`. Conclude with `this` after adjusting the coercions.

Use `⟨hT.trans_lt hlt, fun I hI v i j hij => lt_of_le_of_lt (dim_le_of_primes _ _ fun P hP hle => ?_) hlt⟩` and prove the remaining obligations. Distinguish the cases in `hM : L.ρ.triM ≤ P`. Conclude with `(dim_anti hM).trans hT`. Establish `hoff : L.ρ.OffTri P` using `⟨fun h => hP.ne_top (top_le_iff.1 (h2 ▸ h)), hM⟩`. Establish `hIP : I ≤ L.π P` using `(Ideal.map_le_iff_le_comap (f := L.b)).1 (le_sup_left.trans (le_sup_left.trans hle))`.

Establish `hco : L.ρ.Coin P v i j` using `fun g hg => (le_sup_right.trans hle) (Ideal.subset_span ⟨g, hg, rfl⟩)`. Establish `h` using `(l52 hF hn S x L I hI v i j hij P hP hoff hIP hco).2 (le_sup_right.trans (le_sup_left.trans hle))`. Use `le_of_add_le h ?_` and prove the remaining obligations. Use `hdv v` as an intermediate fact. Apply the tactic sequence `rcases hn with rfl | rfl <;> omega`.
-/
theorem UpperTheory.V.Fr.krull_dim_lt_of_not_le_triangular :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), F.Big C₀ → ¬ S.u.triP ≤ x → ringKrullDim (L.R ⧸ L.ρ.triM) < (n * F.d : ℕ) ∧ ∀ I : Ideal S.B, S.FinLam I → ∀ v i j, i ≠ j → ringKrullDim (L.R ⧸ (I.map L.b ⊔ (maximalIdeal O).map (algebraMap O L.R) ⊔ Ideal.span {y | ∃ g ∈ F.Nv v, y = (L.ρ.ψ v i g : L.R) - L.ρ.ψ v j g})) < (n * F.d : ℕ) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L hB hx
  obtain ⟨h1, h2⟩ := l51 hF hn S x L hx
  obtain ⟨hd, hdv⟩ := hB
  have hlt : ((n * F.d - 1 : ℕ) : WithBot ℕ∞) < (n * F.d : ℕ) := by
    have : n * F.d - 1 < n * F.d := by rcases hn with rfl | rfl <;> omega
    exact_mod_cast this
  have hT : ringKrullDim (L.R ⧸ L.ρ.triM) ≤ (n * F.d - 1 : ℕ) := by
    refine h1.trans ?_
    have : (n - 1) * F.d + 2 + (3 * C₀ + 5) ≤ n * F.d - 1 := by rcases hn with rfl | rfl <;> omega
    exact_mod_cast this
  refine ⟨hT.trans_lt hlt, fun I hI v i j hij => lt_of_le_of_lt (dim_le_of_primes _ _ fun P hP hle => ?_) hlt⟩
  by_cases hM : L.ρ.triM ≤ P
  · exact (dim_anti hM).trans hT
  have hoff : L.ρ.OffTri P := ⟨fun h => hP.ne_top (top_le_iff.1 (h2 ▸ h)), hM⟩
  have hIP : I ≤ L.π P :=
    (Ideal.map_le_iff_le_comap (f := L.b)).1 (le_sup_left.trans (le_sup_left.trans hle))
  have hco : L.ρ.Coin P v i j := fun g hg => (le_sup_right.trans hle) (Ideal.subset_span ⟨g, hg, rfl⟩)
  have h := (l52 hF hn S x L I hI v i j hij P hP hoff hIP hco).2 (le_sup_right.trans (le_sup_left.trans hle))
  refine le_of_add_le h ?_
  have := hdv v
  rcases hn with rfl | rfl <;> omega
