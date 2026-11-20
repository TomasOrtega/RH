import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

/- English proof (translation)
Establish `h1 : ∀ Y ∈ Submodule.span A T, Y.map (algebraMap A F) ∈ S`. Introduce `Y hY`. Proceed by induction on `hY using Submodule.span_induction with`. Consider the case `mem y hy => exact hS y hy`. Consider the case `zero => simp`.

Consider the case `add y z _ _ hy hz`. Establish `: (y + z).map (algebraMap A F) = y.map (algebraMap A F) + z.map (algebraMap A F)`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `S.add_mem hy hz`. Consider the case `smul c y _ hy`. Establish `: (c • y).map (algebraMap A F) = algebraMap A F c • y.map (algebraMap A F)`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `S.smul_mem _ hy`. Introduce `Z hZ`. Establish `hZ' : Z = ∑ i, ∑ j, single i j (Z i j)` using `matrix_eq_sum_single Z`. Rewrite using `[hZ']`.

Use `S.sum_mem fun i _ => S.sum_mem fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)`. Take `⟨s, hs⟩` from `hT (single i j 1) (fun p q => ⟨fun _ => trivial, fun e' => by`. Rewrite using `[Submodule.mem_bot, Matrix.single_apply, if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `e' e⟩)`. Establish `h2` using `S.smul_mem (Z i j * (algebraMap A F (t ^ s))⁻¹) (h1 _ hs)`. Establish `hne : algebraMap A F (t ^ s) ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective A F)]`. Conclude with `pow_ne_zero _ ht`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `p q`. Simplify using `only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]`. Use `split_ifs`. Rewrite using `[mul_one, mul_assoc, inv_mul_cancel₀ hne, mul_one]`.

Simplify using the standard rewrite rules. Establish `: Z i j = 0` using `(hZ i j).2 e`. Simplify using `[this]`.
-/
private theorem hr_span {A F : Type} [CommRing A] [IsDomain A] [Field F] [Algebra A F] [IsFractionRing A F] {n a : ℕ}
    (t : A) (ht : t ≠ 0) (T : Set (Matrix (Fin n) (Fin n) A))
    (hT : ∀ Z ∈ Ev A A n a, ∃ s : ℕ, t ^ s • Z ∈ Submodule.span A T)
    (S : Submodule F (Matrix (Fin n) (Fin n) F)) (hS : ∀ Y ∈ T, Y.map (algebraMap A F) ∈ S) :
    Ev F F n a ≤ S := by
  have h1 : ∀ Y ∈ Submodule.span A T, Y.map (algebraMap A F) ∈ S := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem y hy => exact hS y hy
    | zero => simp
    | add y z _ _ hy hz =>
      have : (y + z).map (algebraMap A F) = y.map (algebraMap A F) + z.map (algebraMap A F) := by
        ext i j; simp
      rw [this]; exact S.add_mem hy hz
    | smul c y _ hy =>
      have : (c • y).map (algebraMap A F) = algebraMap A F c • y.map (algebraMap A F) := by
        ext i j; simp
      rw [this]; exact S.smul_mem _ hy
  intro Z hZ
  have hZ' : Z = ∑ i, ∑ j, single i j (Z i j) := matrix_eq_sum_single Z
  rw [hZ']
  refine S.sum_mem fun i _ => S.sum_mem fun j _ => ?_
  by_cases e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
  · obtain ⟨s, hs⟩ := hT (single i j 1) (fun p q => ⟨fun _ => trivial, fun e' => by
      rw [Submodule.mem_bot, Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact e' e⟩)
    have h2 := S.smul_mem (Z i j * (algebraMap A F (t ^ s))⁻¹) (h1 _ hs)
    have hne : algebraMap A F (t ^ s) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective A F)]
      exact pow_ne_zero _ ht
    convert h2 using 1
    ext p q
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one, mul_assoc, inv_mul_cancel₀ hne, mul_one]
    · simp
  · have : Z i j = 0 := (hZ i j).2 e
    simp [this]

/- English proof (translation)
Introduce `l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hs H Z`. Establish `hsm : ∀ (b : Bh) (Y : Matrix (Fin n) (Fin n) (FractionRing x.A)), b • Y = algebraMap Bh (FractionRing x.A) b • Y`. Introduce `b Y`. Use extensionality with `i j`. Simplify using `[Algebra.smul_def]`.

Prove the components needed by the constructor for the conclusion. Set `S : Submodule (FractionRing x.A) (Matrix (Fin n) (Fin n) (FractionRing x.A))` to `{ carrier := {Z | ∃ y, H.r y = Z} add_mem' := by`. Introduce and unpack `_ _ ⟨y, rfl⟩ ⟨z, rfl⟩`. Conclude with `⟨y + z, map_add _ _ _⟩`. Use the proof step `zero_mem' := ⟨0, map_zero _⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `c _ ⟨y, rfl⟩`. Take `⟨b, rfl⟩` from `hs c`. Conclude with `⟨b • y, by rw [map_smul, hsm]⟩ }`. Introduce `hZ`.

Use `hr_span (A := x.A) x.t PowerSeries.X_ne_zero _ x.span S ?_ hZ` and prove the remaining obligations. Introduce and unpack `_ ⟨g, -, rfl⟩`. Take `⟨g', hg'⟩` from `h.surj g.1`. Establish `hm : g' ∈ G.η.ker`. Establish `h1` using `h.η g'`.

Rewrite `h1` using `[hg']`. Rewrite using `[MonoidHom.mem_ker, ← h1]`. Conclude with `g.2`. Establish `: h.p₀ ⟨g', hm⟩ = g` using `Subtype.ext hg'`. Conclude with `⟨_, by rw [← this]; exact H.r_ι ⟨g', hm⟩⟩`.

Introduce and unpack `⟨y, rfl⟩`. Take `⟨z, rfl⟩` from `H.surj y`. Proceed by induction on `z using MonoidAlgebra.induction_on with`. Consider the case `of g`. Use `H.r_ι g` as an intermediate fact.

Rewrite using `[MonoidAlgebra.of_apply, this]`. Introduce `i j`. Use `⟨fun _ => trivial, fun e => ?_⟩` and prove the remaining obligations. Establish `h0 : mat x.ρ (h.p₀ g) i j = 0` using `(x.blk (h.p₀ g) i j).2 e`. Rewrite using `[Submodule.mem_bot, Matrix.map_apply, h0, map_zero]`.

Consider the case `add f g hf hg`. Rewrite using `[map_add, map_add]`. Conclude with `Submodule.add_mem _ hf hg`. Consider the case `smul b f hf`. Rewrite using `[map_smul, map_smul, hsm]`.

Conclude with `Submodule.smul_mem _ _ hf`.
-/
theorem UpperTheory.V.Pa.hat_range :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)], Function.Surjective (algebraMap Bh (FractionRing x.A)) → ∀ H : Hat h x u.D P.ker Bh (G.frame.eps O B), ∀ Z, Z ∈ Ev (FractionRing x.A) (FractionRing x.A) n x.a ↔ ∃ y, H.r y = Z := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hs H Z
  have hsm : ∀ (b : Bh) (Y : Matrix (Fin n) (Fin n) (FractionRing x.A)),
      b • Y = algebraMap Bh (FractionRing x.A) b • Y := by
    intro b Y
    ext i j
    simp [Algebra.smul_def]
  constructor
  · let S : Submodule (FractionRing x.A) (Matrix (Fin n) (Fin n) (FractionRing x.A)) :=
      { carrier := {Z | ∃ y, H.r y = Z}
        add_mem' := by
          rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩
          exact ⟨y + z, map_add _ _ _⟩
        zero_mem' := ⟨0, map_zero _⟩
        smul_mem' := by
          rintro c _ ⟨y, rfl⟩
          obtain ⟨b, rfl⟩ := hs c
          exact ⟨b • y, by rw [map_smul, hsm]⟩ }
    intro hZ
    refine hr_span (A := x.A) x.t PowerSeries.X_ne_zero _ x.span S ?_ hZ
    rintro _ ⟨g, -, rfl⟩
    obtain ⟨g', hg'⟩ := h.surj g.1
    have hm : g' ∈ G.η.ker := by
      have h1 := h.η g'
      rw [hg'] at h1
      rw [MonoidHom.mem_ker, ← h1]
      exact g.2
    have : h.p₀ ⟨g', hm⟩ = g := Subtype.ext hg'
    exact ⟨_, by rw [← this]; exact H.r_ι ⟨g', hm⟩⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := H.surj y
    induction z using MonoidAlgebra.induction_on with
    | of g =>
      have := H.r_ι g
      rw [MonoidAlgebra.of_apply, this]
      intro i j
      refine ⟨fun _ => trivial, fun e => ?_⟩
      have h0 : mat x.ρ (h.p₀ g) i j = 0 := (x.blk (h.p₀ g) i j).2 e
      rw [Submodule.mem_bot, Matrix.map_apply, h0, map_zero]
    | add f g hf hg =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hf hg
    | smul b f hf =>
      rw [map_smul, map_smul, hsm]
      exact Submodule.smul_mem _ _ hf
