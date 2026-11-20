import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FinAm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LemmaB
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CardEqPowLength

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Take `⟨e, he⟩` from `UpperTheory.V.AlgebraTools.lemma_B f`. Use `⟨e, ?_⟩` and prove the remaining obligations. Introduce `m E' _ _ r T hker hT`. Use `set p := IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E) with hp`. Use `set W := ⨅ s, Submodule.comap (f s) p with hW`.

Establish `hle` using `he m`. Establish `hne : Module.length A (Submodule.map p.mkQ W) ≠ ⊤` using `ne_top_of_le_ne_top (ENat.coe_ne_top _) hle`. Take `⟨hfin_iff, hcard⟩` from `UpperTheory.V.AlgebraTools.card_eq_pow_length (A := A) (X := Submodule.map p.mkQ W)`. Establish `hfin : Finite (Submodule.map p.mkQ W)` using `hfin_iff.2 hne`. Establish `hfs : (Submodule.map p.mkQ W : Set (E ⧸ p)).Finite` using `Set.finite_coe_iff.1 hfin`.

Set `r'` to `p.liftQ r (le_of_eq hker.symm)`. Establish `hinj : Function.Injective r'` using `LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot' (p := p) (f := r) hker.symm)`. Establish `hsub : T ⊆ r' '' (Submodule.map p.mkQ W : Set (E ⧸ p))`. Introduce `Y hY`. Take `⟨Z, hZ, hZs⟩` from `hT Y hY`.

Use `⟨p.mkQ Z, ⟨Z, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, hW, Submodule.mem_iInf]`. Introduce `s`. Rewrite using `[Submodule.mem_comap, ← hker, LinearMap.mem_ker]`. Conclude with `hZs s`.

Simplify using `[r', hZ]`. Establish `htoNat : (Module.length A (Submodule.map p.mkQ W)).toNat ≤ m * Module.finrank A (⨅ s, LinearMap.ker (f s) : Submodule A E) + e`. Establish `h1 : (((Module.length A (Submodule.map p.mkQ W)).toNat : ℕ) : ℕ∞) ≤ ((Module.finrank A (⨅ s, LinearMap.ker (f s) : Submodule A E) * m + e : ℕ) : ℕ∞)`. Rewrite using `[ENat.coe_toNat hne]`. Conclude with `hle`.

Rewrite using `[mul_comm]`. Conclude with `Nat.cast_le.1 h1`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem fixBd_abs {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Finite (IsLocalRing.ResidueField A)] {E S : Type} [AddCommGroup E] [Module A E] [Module.Finite A E]
    (f : S → E →ₗ[A] E) : ∃ C : ℕ, ∀ (m : ℕ) (E' : Type) [AddCommGroup E'] [Module A E'] (r : E →ₗ[A] E')
      (T : Set E'), LinearMap.ker r = IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E) →
      (∀ Y ∈ T, ∃ Z, r Z = Y ∧ ∀ s, r (f s Z) = 0) →
      T.ncard ≤ Nat.card (IsLocalRing.ResidueField A) ^
        (m * Module.finrank A (⨅ s, LinearMap.ker (f s) : Submodule A E) + C) := by
  obtain ⟨e, he⟩ := UpperTheory.V.AlgebraTools.lemma_B f
  refine ⟨e, ?_⟩
  intro m E' _ _ r T hker hT
  set p := IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A E) with hp
  set W := ⨅ s, Submodule.comap (f s) p with hW
  have hle := he m
  have hne : Module.length A (Submodule.map p.mkQ W) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hle
  obtain ⟨hfin_iff, hcard⟩ := UpperTheory.V.AlgebraTools.card_eq_pow_length (A := A) (X := Submodule.map p.mkQ W)
  have hfin : Finite (Submodule.map p.mkQ W) := hfin_iff.2 hne
  have hfs : (Submodule.map p.mkQ W : Set (E ⧸ p)).Finite := Set.finite_coe_iff.1 hfin
  let r' := p.liftQ r (le_of_eq hker.symm)
  have hinj : Function.Injective r' :=
    LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot' (p := p) (f := r) hker.symm)
  have hsub : T ⊆ r' '' (Submodule.map p.mkQ W : Set (E ⧸ p)) := by
    intro Y hY
    obtain ⟨Z, hZ, hZs⟩ := hT Y hY
    refine ⟨p.mkQ Z, ⟨Z, ?_, rfl⟩, ?_⟩
    · rw [SetLike.mem_coe, hW, Submodule.mem_iInf]
      intro s
      rw [Submodule.mem_comap, ← hker, LinearMap.mem_ker]
      exact hZs s
    · simp [r', hZ]
  have htoNat : (Module.length A (Submodule.map p.mkQ W)).toNat ≤
      m * Module.finrank A (⨅ s, LinearMap.ker (f s) : Submodule A E) + e := by
    have h1 : (((Module.length A (Submodule.map p.mkQ W)).toNat : ℕ) : ℕ∞) ≤
        ((Module.finrank A (⨅ s, LinearMap.ker (f s) : Submodule A E) * m + e : ℕ) : ℕ∞) := by
      rw [ENat.coe_toNat hne]
      exact hle
    rw [mul_comm]
    exact Nat.cast_le.1 h1
  calc T.ncard ≤ (r' '' (Submodule.map p.mkQ W : Set (E ⧸ p))).ncard :=
        Set.ncard_le_ncard hsub (hfs.image _)
    _ = (Submodule.map p.mkQ W : Set (E ⧸ p)).ncard := Set.ncard_image_of_injective _ hinj
    _ = Nat.card (Submodule.map p.mkQ W) := (Nat.card_coe_set_eq _).symm
    _ = Nat.card (IsLocalRing.ResidueField A) ^ (Module.length A (Submodule.map p.mkQ W)).toNat :=
        hcard hfin
    _ ≤ _ := Nat.pow_le_pow_right Nat.card_pos htoNat

/- English proof (translation)
Establish `h1 : (algebraMap A (DD X g) c).a = algebraMap A X c` using `rfl`. Establish `h2 : (algebraMap A (DD X g) c).ep = 0` using `rfl`. Establish `h3 : (algebraMap A (DD X g) c).ep' = 0` using `rfl`. Establish `h4 : (algebraMap A (DD X g) c).eta = 0` using `rfl`. Rewrite using `[Algebra.smul_def]`.

Apply the tactic sequence `ext <;> simp [h1, h2, h3, h4, Algebra.smul_def]`.
-/
private theorem fixBd_smul {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g : ℕ} (c : A) (y : DD X g) :
    c • y = ⟨c • y.a, fun j => c • y.ep j, fun j => c • y.ep' j, c • y.eta⟩ := by
  have h1 : (algebraMap A (DD X g) c).a = algebraMap A X c := rfl
  have h2 : (algebraMap A (DD X g) c).ep = 0 := rfl
  have h3 : (algebraMap A (DD X g) c).ep' = 0 := rfl
  have h4 : (algebraMap A (DD X g) c).eta = 0 := rfl
  rw [Algebra.smul_def]
  ext <;> simp [h1, h2, h3, h4, Algebra.smul_def]

/- English proof (translation)
Set `L : (A × (Fin g → A)) × ((Fin g → A) × A) →ₗ[A] DD A g` to `{ toFun := fun p => ⟨p.1.1, p.1.2, p.2.1, p.2.2⟩ map_add' := fun p q => rfl map_smul' := fun c p => by`. Rewrite using `[fixBd_smul]`. Use `rfl }`. Conclude with `Module.Finite.of_surjective L fun y => ⟨((y.a, y.ep), (y.ep', y.eta)), rfl⟩`.
-/
private theorem fixBd_fin (A : Type) [CommRing A] (g : ℕ) : Module.Finite A (DD A g) := by
  let L : (A × (Fin g → A)) × ((Fin g → A) × A) →ₗ[A] DD A g :=
    { toFun := fun p => ⟨p.1.1, p.1.2, p.2.1, p.2.2⟩
      map_add' := fun p q => rfl
      map_smul' := fun c p => by
        rw [fixBd_smul]
        rfl }
  exact Module.Finite.of_surjective L fun y => ⟨((y.a, y.ep), (y.ep', y.eta)), rfl⟩

private def fixBd_q (A X : Type) [CommRing A] [CommRing X] [Algebra A X] (g : ℕ) (b₁ b₂ b₃ b₄ : Bool) :
    DD X g →ₗ[A] DD X g where
  toFun y := ⟨if b₁ then 0 else y.a, fun j => if b₂ then 0 else y.ep j, fun j => if b₃ then 0 else y.ep' j,
    if b₄ then 0 else y.eta⟩
  map_add' y z := by ext <;> simp <;> split_ifs <;> simp
  map_smul' c y := by
    rw [fixBd_smul, fixBd_smul]
    ext <;> simp

/- English proof (translation)
Establish `e : fixBd_q A X g b₁ b₂ b₃ b₄ y = ⟨if b₁ then 0 else y.a, fun j => if b₂ then 0 else y.ep j, fun j => if b₃ then 0 else y.ep' j, if b₄ then 0 else y.eta⟩` using `rfl`. Establish `z1 : (0 : DD X g).a = 0` using `rfl`. Establish `z2 : (0 : DD X g).ep = 0` using `rfl`. Establish `z3 : (0 : DD X g).ep' = 0` using `rfl`. Establish `z4 : (0 : DD X g).eta = 0` using `rfl`.

Use `show _ ↔ ((b₁ = false → y.a = 0) ∧ (b₂ = false → y.ep = 0) ∧ (b₃ = false → y.ep' = 0) ∧ (b₄ = false → y.eta = 0))`. Rewrite using `[e, DD.ext_iff, z1, z2, z3, z4]`. Apply the tactic sequence `cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;> simp [funext_iff]`.
-/
private theorem fixBd_q_zero {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g : ℕ} (b₁ b₂ b₃ b₄ : Bool)
    (y : DD X g) : fixBd_q A X g b₁ b₂ b₃ b₄ y = 0 ↔ y ∈ ddPart A X g b₁ b₂ b₃ b₄ := by
  have e : fixBd_q A X g b₁ b₂ b₃ b₄ y = ⟨if b₁ then 0 else y.a, fun j => if b₂ then 0 else y.ep j,
      fun j => if b₃ then 0 else y.ep' j, if b₄ then 0 else y.eta⟩ := rfl
  have z1 : (0 : DD X g).a = 0 := rfl
  have z2 : (0 : DD X g).ep = 0 := rfl
  have z3 : (0 : DD X g).ep' = 0 := rfl
  have z4 : (0 : DD X g).eta = 0 := rfl
  show _ ↔ ((b₁ = false → y.a = 0) ∧ (b₂ = false → y.ep = 0) ∧ (b₃ = false → y.ep' = 0) ∧
    (b₄ = false → y.eta = 0))
  rw [e, DD.ext_iff, z1, z2, z3, z4]
  cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;> simp [funext_iff]

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [fixBd_q] <;> split_ifs <;> simp`.
-/
private theorem fixBd_q_map {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g : ℕ} (b₁ b₂ b₃ b₄ : Bool)
    (f : A →ₐ[A] X) (y : DD A g) :
    DD.map g f (fixBd_q A A g b₁ b₂ b₃ b₄ y) = fixBd_q A X g b₁ b₂ b₃ b₄ (DD.map g f y) := by
  ext <;> simp [fixBd_q] <;> split_ifs <;> simp

private def fixBd_p {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (n a : ℕ) (q₁ q₂ : R →ₗ[A] R) :
    Matrix (Fin n) (Fin n) R →ₗ[A] Matrix (Fin n) (Fin n) R where
  toFun Z := Matrix.of fun i j => if (((i : ℕ) < a) ↔ ((j : ℕ) < a)) then q₁ (Z i j) else q₂ (Z i j)
  map_add' y z := by ext i j; simp; split_ifs <;> simp
  map_smul' c y := by ext i j; simp

/- English proof (translation)
Establish `key : ∀ i j, fixBd_p n a (fixBd_q A X g b₁ b₂ b₃ b₄) (fixBd_q A X g c₁ c₂ c₃ c₄) Z i j = if (((i : ℕ) < a) ↔ ((j : ℕ) < a)) then fixBd_q A X g b₁ b₂ b₃ b₄ (Z i j) else fixBd_q A X g c₁ c₂ c₃ c₄ (Z i j)` using `fun i j => rfl`. Establish `mem : Z ∈ blkMat n a (ddPart A X g b₁ b₂ b₃ b₄) (ddPart A X g c₁ c₂ c₃ c₄) ↔ ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j ∈ ddPart A X g b₁ b₂ b₃ b₄) ∧ (¬((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j ∈ ddPart A X g c₁ c₂ c₃ c₄)` using `Iff.rfl`. Rewrite using `[mem]`. Prove the components needed by the constructor for the conclusion. Introduce `hZ i j`.

Establish `h0 : fixBd_p n a (fixBd_q A X g b₁ b₂ b₃ b₄) (fixBd_q A X g c₁ c₂ c₃ c₄) Z i j = 0`. Rewrite using `[hZ]`. Both sides reduce to the same expression. Rewrite `h0` using `[key]`. Prove the components needed by the constructor for the conclusion.

Introduce `hc`. Rewrite `h0` using `[if_pos hc]`. Conclude with `(fixBd_q_zero _ _ _ _ _).1 h0`. Introduce `hc`. Rewrite `h0` using `[if_neg hc]`.

Conclude with `(fixBd_q_zero _ _ _ _ _).1 h0`. Introduce `hZ`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Rewrite using `[key]`. Use `split_ifs with hc`.

Conclude with `(fixBd_q_zero _ _ _ _ _).2 ((hZ i j).1 hc)`. Conclude with `(fixBd_q_zero _ _ _ _ _).2 ((hZ i j).2 hc)`.
-/
private theorem fixBd_p_zero {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g : ℕ} (n a : ℕ)
    (b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ : Bool) (Z : Matrix (Fin n) (Fin n) (DD X g)) :
    fixBd_p n a (fixBd_q A X g b₁ b₂ b₃ b₄) (fixBd_q A X g c₁ c₂ c₃ c₄) Z = 0 ↔
      Z ∈ blkMat n a (ddPart A X g b₁ b₂ b₃ b₄) (ddPart A X g c₁ c₂ c₃ c₄) := by
  have key : ∀ i j, fixBd_p n a (fixBd_q A X g b₁ b₂ b₃ b₄) (fixBd_q A X g c₁ c₂ c₃ c₄) Z i j =
      if (((i : ℕ) < a) ↔ ((j : ℕ) < a)) then fixBd_q A X g b₁ b₂ b₃ b₄ (Z i j)
      else fixBd_q A X g c₁ c₂ c₃ c₄ (Z i j) := fun i j => rfl
  have mem : Z ∈ blkMat n a (ddPart A X g b₁ b₂ b₃ b₄) (ddPart A X g c₁ c₂ c₃ c₄) ↔
      ∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j ∈ ddPart A X g b₁ b₂ b₃ b₄) ∧
        (¬((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j ∈ ddPart A X g c₁ c₂ c₃ c₄) := Iff.rfl
  rw [mem]
  constructor
  · intro hZ i j
    have h0 : fixBd_p n a (fixBd_q A X g b₁ b₂ b₃ b₄) (fixBd_q A X g c₁ c₂ c₃ c₄) Z i j = 0 := by
      rw [hZ]
      rfl
    rw [key] at h0
    constructor
    · intro hc
      rw [if_pos hc] at h0
      exact (fixBd_q_zero _ _ _ _ _).1 h0
    · intro hc
      rw [if_neg hc] at h0
      exact (fixBd_q_zero _ _ _ _ _).1 h0
  · intro hZ
    refine Matrix.ext fun i j => ?_
    rw [key]
    split_ifs with hc
    · exact (fixBd_q_zero _ _ _ _ _).2 ((hZ i j).1 hc)
    · exact (fixBd_q_zero _ _ _ _ _).2 ((hZ i j).2 hc)

/- English proof (translation)
Introduce `y`. Establish `hs` using `Ideal.Quotient.mkₐ_surjective A I`. Use `⟨⟨Function.surjInv hs y.a, fun j => Function.surjInv hs (y.ep j), fun j => Function.surjInv hs (y.ep' j), Function.surjInv hs y.eta⟩, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp only [DD.map_a, DD.map_ep, DD.map_ep', DD.map_eta] <;> exact Function.surjInv_eq hs _`.
-/
private theorem fixBd_surj {A : Type} [CommRing A] (I : Ideal A) (g : ℕ) :
    Function.Surjective (DD.map g (Ideal.Quotient.mkₐ A I)) := by
  intro y
  have hs := Ideal.Quotient.mkₐ_surjective A I
  refine ⟨⟨Function.surjInv hs y.a, fun j => Function.surjInv hs (y.ep j),
    fun j => Function.surjInv hs (y.ep' j), Function.surjInv hs y.eta⟩, ?_⟩
  ext <;> simp only [DD.map_a, DD.map_ep, DD.map_ep', DD.map_eta] <;> exact Function.surjInv_eq hs _

/- English proof (translation)
Establish `z1 : (0 : DD (A ⧸ Ideal.span {c}) g).a = 0` using `rfl`. Establish `z2 : (0 : DD (A ⧸ Ideal.span {c}) g).ep = 0` using `rfl`. Establish `z3 : (0 : DD (A ⧸ Ideal.span {c}) g).ep' = 0` using `rfl`. Establish `z4 : (0 : DD (A ⧸ Ideal.span {c}) g).eta = 0` using `rfl`. Establish `ha : ∀ w : A, Ideal.Quotient.mkₐ A (Ideal.span {c}) w = 0 → ∃ z, c * z = w`.

Introduce `w hw`. Rewrite `hw` using `[Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']`. Take `⟨z, hz⟩` from `hw`. Conclude with `⟨z, by rw [mul_comm]; exact hz⟩`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Rewrite `hy` using `[DD.ext_iff, z1, z2, z3, z4]`. Take `⟨h1, h2, h3, h4⟩` from `hy`. Rewrite `h1` using `[DD.map_a]`. Rewrite `h4` using `[DD.map_eta]`.

Take `⟨za, hza⟩` from `ha _ h1`. Take `⟨zeta, hzeta⟩` from `ha _ h4`. Establish `hep : ∀ j, ∃ z, c * z = y.ep j` using `fun j => ha _ (by`. Establish `hj` using `congrFun h2 j`. Rewrite `hj` using `[DD.map_ep]`.

Conclude with `hj)`. Establish `hep' : ∀ j, ∃ z, c * z = y.ep' j` using `fun j => ha _ (by`. Establish `hj` using `congrFun h3 j`. Rewrite `hj` using `[DD.map_ep']`. Conclude with `hj)`.

Use `choose zep hzep using hep`. Use `choose zep' hzep' using hep'`. Use `⟨⟨za, zep, zep', zeta⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[fixBd_smul]`. Apply the tactic sequence `ext <;> simp [smul_eq_mul, hza, hzep, hzep', hzeta]`.

Introduce and unpack `⟨z, rfl⟩`. Rewrite using `[fixBd_smul]`. Apply the tactic sequence `ext <;> simp [DD.map_a, DD.map_ep, DD.map_ep', DD.map_eta, z1, z2, z3, z4, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, smul_eq_mul]`.
-/
private theorem fixBd_ker {A : Type} [CommRing A] (c : A) (g : ℕ) (y : DD A g) :
    DD.map g (Ideal.Quotient.mkₐ A (Ideal.span {c})) y = 0 ↔ ∃ z, c • z = y := by
  have z1 : (0 : DD (A ⧸ Ideal.span {c}) g).a = 0 := rfl
  have z2 : (0 : DD (A ⧸ Ideal.span {c}) g).ep = 0 := rfl
  have z3 : (0 : DD (A ⧸ Ideal.span {c}) g).ep' = 0 := rfl
  have z4 : (0 : DD (A ⧸ Ideal.span {c}) g).eta = 0 := rfl
  have ha : ∀ w : A, Ideal.Quotient.mkₐ A (Ideal.span {c}) w = 0 → ∃ z, c * z = w := by
    intro w hw
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hw
    obtain ⟨z, hz⟩ := hw
    exact ⟨z, by rw [mul_comm]; exact hz⟩
  constructor
  · intro hy
    rw [DD.ext_iff, z1, z2, z3, z4] at hy
    obtain ⟨h1, h2, h3, h4⟩ := hy
    rw [DD.map_a] at h1
    rw [DD.map_eta] at h4
    obtain ⟨za, hza⟩ := ha _ h1
    obtain ⟨zeta, hzeta⟩ := ha _ h4
    have hep : ∀ j, ∃ z, c * z = y.ep j := fun j => ha _ (by
      have hj := congrFun h2 j
      rw [DD.map_ep] at hj
      exact hj)
    have hep' : ∀ j, ∃ z, c * z = y.ep' j := fun j => ha _ (by
      have hj := congrFun h3 j
      rw [DD.map_ep'] at hj
      exact hj)
    choose zep hzep using hep
    choose zep' hzep' using hep'
    refine ⟨⟨za, zep, zep', zeta⟩, ?_⟩
    rw [fixBd_smul]
    ext <;> simp [smul_eq_mul, hza, hzep, hzep', hzeta]
  · rintro ⟨z, rfl⟩
    rw [fixBd_smul]
    ext <;> simp [DD.map_a, DD.map_ep, DD.map_ep', DD.map_eta, z1, z2, z3, z4, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, smul_eq_mul]

/- English proof (translation)
Introduce `l _ F n x k V b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ S e P Q tr hV`. Use `haveI : Module.Finite x.A (DD x.A k.g) := fixBd_fin x.A k.g`. Use `haveI : Module.Finite x.A (Matrix (Fin n) (Fin n) (DD x.A k.g)) := (inferInstance : Module.Finite x.A (Fin n → Fin n → DD x.A k.g))`. Use `haveI : Finite (IsLocalRing.ResidueField x.A) := Finite.of_equiv x.K (PowerSeries.residueFieldOfPowerSeries).toEquiv.symm`. Establish `hRes : Nat.card (IsLocalRing.ResidueField x.A) = Nat.card x.K` using `Nat.card_congr (PowerSeries.residueFieldOfPowerSeries).toEquiv`.

Set `f : Option (Option S) → (Matrix (Fin n) (Fin n) (DD x.A k.g) →ₗ[x.A] Matrix (Fin n) (Fin n) (DD x.A k.g))` to `fun o => match o with`. Consider the case `none => fixBd_p n x.a (fixBd_q x.A x.A k.g b₁ b₂ b₃ b₄) (fixBd_q x.A x.A k.g c₁ c₂ c₃ c₄)`. Consider the case `some none => if tr then (Matrix.transposeLinearEquiv (Fin n) (Fin n) x.A (DD x.A k.g)).toLinearMap + LinearMap.id else 0`. Consider the case `some (some s) => e s • ((LinearMap.mulLeft x.A (P s)).comp (LinearMap.mulRight x.A (Q s))) - LinearMap.id`. Take `⟨C, hC⟩` from `fixBd_abs (A := x.A) (E := Matrix (Fin n) (Fin n) (DD x.A k.g)) f`.

Use `⟨C, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `have hT0 : LinearMap.ker (f (some none)) = (if tr then LinearMap.ker ((Matrix.transposeLinearEquiv (Fin n) (Fin n) x.A (DD x.A k.g)).toLinearMap + LinearMap.id) else ⊤) := by show LinearMap.ker (if tr then _ else 0) = _ split_ifs <;> simp`. Establish `hK : (⨅ o, LinearMap.ker (f o)) = (V ⊓ (if tr then LinearMap.ker ((Matrix.transposeLinearEquiv (Fin n) (Fin n) x.A (DD x.A k.g)).toLinearMap + LinearMap.id) else ⊤) ⊓ ⨅ s, LinearMap.ker (e s • ((LinearMap.mulLeft x.A (P s)).comp (LinearMap.mulRight x.A (Q s))) - LinearMap.id) : S …`. Use extensionality with `Z`. Establish `e0 : Z ∈ LinearMap.ker (f none) ↔ Z ∈ V`.

Rewrite using `[LinearMap.mem_ker, hV]`. Conclude with `fixBd_p_zero n x.a b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ Z`. Establish `e1 : Z ∈ LinearMap.ker (f (some none)) ↔ Z ∈ (if tr then LinearMap.ker ((Matrix.transposeLinearEquiv (Fin n) (Fin n) x.A (DD x.A k.g)).toLinearMap + LinearMap.id) else ⊤)`. Rewrite using `[hT0]`. Rewrite using `[Submodule.mem_iInf, Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_iInf]`.

Prove the components needed by the constructor for the conclusion. Introduce `hZ`. Conclude with `⟨⟨e0.1 (hZ none), e1.1 (hZ (some none))⟩, fun s => hZ (some (some s))⟩`. Introduce and unpack `⟨⟨h0, h1⟩, h2⟩ o`. Break down `o with _ | _ | s` into its components or cases.

Conclude with `e0.2 h0`. Conclude with `e1.2 h1`. Conclude with `h2 s`. Rewrite using `[← hK, ← hRes]`. Introduce `m`.

Set `r : Matrix (Fin n) (Fin n) (DD x.A k.g) →ₗ[x.A] Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)` to `(x.redD k.g m).mapMatrix.toLinearMap`. Establish `hker : LinearMap.ker r = IsLocalRing.maximalIdeal x.A ^ m • (⊤ : Submodule x.A (Matrix (Fin n) (Fin n) (DD x.A k.g)))`. Rewrite using `[PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]`. Use extensionality with `Z`. Rewrite using `[LinearMap.mem_ker, Submodule.mem_smul_pointwise_iff_exists]`.

Prove the components needed by the constructor for the conclusion. Introduce `hZ`. Establish `h1 : ∀ i j, ∃ z, (PowerSeries.X : x.A) ^ m • z = Z i j` using `fun i j => (fixBd_ker ((PowerSeries.X : x.A) ^ m) k.g (Z i j)).1 (congrFun (congrFun hZ i) j)`. Use `choose W hW using h1`. Conclude with `⟨Matrix.of W, Submodule.mem_top, Matrix.ext fun i j => hW i j⟩`.

Introduce and unpack `⟨W, -, rfl⟩`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Conclude with `(fixBd_ker ((PowerSeries.X : x.A) ^ m) k.g _).2 ⟨W i j, rfl⟩`. Apply `hC m _ r _ hker` to reduce the goal to its premises. Introduce `Y hY`.

Establish `hl : ∀ i j, ∃ z, x.redD k.g m z = Y i j` using `fun i j => fixBd_surj _ k.g (Y i j)`. Use `choose Z0 hZ0 using hl`. Establish `hZY : r (Matrix.of Z0) = Y` using `Matrix.ext fun i j => hZ0 i j`. Use `⟨Matrix.of Z0, hZY, ?_⟩` and prove the remaining obligations. Introduce `o`.

Break down `o with _ | _ | s` into its components or cases. Establish `hp : r (fixBd_p n x.a (fixBd_q x.A x.A k.g b₁ b₂ b₃ b₄) (fixBd_q x.A x.A k.g c₁ c₂ c₃ c₄) (Matrix.of Z0)) = fixBd_p n x.a (fixBd_q x.A (x.Am m) k.g b₁ b₂ b₃ b₄) (fixBd_q x.A (x.Am m) k.g c₁ c₂ c₃ c₄) Y`. Rewrite using `[← hZY]`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Use `show x.redD k.g m (if _ then _ else _) = if _ then _ else _`.

Use `split_ifs`. Conclude with `fixBd_q_map _ _ _ _ _ _`. Conclude with `fixBd_q_map _ _ _ _ _ _`. Use `show r (fixBd_p n x.a (fixBd_q x.A x.A k.g b₁ b₂ b₃ b₄) (fixBd_q x.A x.A k.g c₁ c₂ c₃ c₄) (Matrix.of Z0)) = 0`. Rewrite using `[hp]`.

Conclude with `(fixBd_p_zero n x.a b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ Y).2 hY.1`. Use `show r ((if tr then (Matrix.transposeLinearEquiv (Fin n) (Fin n) x.A (DD x.A k.g)).toLinearMap + LinearMap.id else 0 : Matrix (Fin n) (Fin n) (DD x.A k.g) →ₗ[x.A] Matrix (Fin n) (Fin n) (DD x.A k.g)) (Matrix.of Z0)) = 0 split_ifs with htr`. Establish `ht : r ((Matrix.transposeLinearEquiv (Fin n) (Fin n) x.A (DD x.A k.g)).toLinearMap (Matrix.of Z0)) = Yᵀ`. Rewrite using `[← hZY]`. Both sides reduce to the same expression.

Rewrite using `[LinearMap.add_apply, map_add, LinearMap.id_apply, hZY, ht, hY.2.1 htr, neg_add_cancel]`. Simplify using the standard rewrite rules. Use `show r ((e s • ((LinearMap.mulLeft x.A (P s)).comp (LinearMap.mulRight x.A (Q s))) - LinearMap.id : Matrix (Fin n) (Fin n) (DD x.A k.g) →ₗ[x.A] Matrix (Fin n) (Fin n) (DD x.A k.g)) (Matrix.of Z0)) = 0`. Establish `hm : ∀ M : Matrix (Fin n) (Fin n) (DD x.A k.g), (x.redD k.g m).mapMatrix M = M.map (fun y => ⟨algebraMap x.A (x.Am m) y.a, fun j => algebraMap x.A (x.Am m) (y.ep j), fun j => algebraMap x.A (x.Am m) (y.ep' j), algebraMap x.A (x.Am m) y.eta⟩)` using `fun M => rfl`. Establish `hZY' : (x.redD k.g m).mapMatrix (Matrix.of Z0) = Y` using `hZY`.

Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, LinearMap.id_apply]`. Use `show (x.redD k.g m).mapMatrix (e s • (P s * (Matrix.of Z0 * Q s)) - Matrix.of Z0) = 0`. Rewrite using `[map_sub, map_smul, map_mul, map_mul, hZY', hm (P s), hm (Q s), ← mul_assoc, hY.2.2 s, sub_self]`.
-/
theorem UpperTheory.V.Pa.fixBd :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (V : Submodule x.A (Matrix (Fin n) (Fin n) (DD x.A k.g))) (b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ : Bool) (S : Type) (e : S → x.A) (P Q : S → Matrix (Fin n) (Fin n) (DD x.A k.g)) (tr : Bool), V = blkMat n x.a (ddPart x.A x.A k.g b₁ b₂ b₃ b₄) (ddPart x.A x.A k.g c₁ c₂ c₃ c₄) → ∃ C : ℕ, ∀ m, {Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) | Y ∈ blkMat n x.a (ddPart x.A (x.Am m) k.g b₁ b₂ b₃ b₄) (ddPart x.A (x.Am m) k.g c₁ c₂ c₃ c₄) ∧ (tr = true → Yᵀ = -Y) ∧ ∀ s, e s • ((P s).map (fun y => ⟨algebraMap x.A (x.Am m) y.a, fun j => algebraMap x.A (x.Am m) (y.ep j), fun j => algebraMap x.A (x.Am m) (y.ep' j), algebraMap x.A (x.Am m) y.eta⟩) * Y * (Q s).map (fun y => ⟨algebraMap x.A (x.Am m) y.a, fun j => algebraMap x.A (x.Am m) (y.ep j), fun j => algebraMap x.A (x.Am m) (y.ep' j), algebraMap x.A (x.Am m) y.eta⟩)) = Y}.ncard ≤ Nat.card x.K ^ (m * Module.finrank x.A (V ⊓ (if tr then LinearMap.ker ((Matrix.transposeLinearEquiv (Fin n) (Fin n) x.A (DD x.A k.g)).toLinearMap + LinearMap.id) else ⊤) ⊓ ⨅ s, LinearMap.ker (e s • ((LinearMap.mulLeft x.A (P s)).comp (LinearMap.mulRight x.A (Q s))) - LinearMap.id) : Submodule x.A (Matrix (Fin n) (Fin n) (DD x.A k.g))) + C) := by
  intro l _ F n x k V b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ S e P Q tr hV
  haveI : Module.Finite x.A (DD x.A k.g) := fixBd_fin x.A k.g
  haveI : Module.Finite x.A (Matrix (Fin n) (Fin n) (DD x.A k.g)) :=
    (inferInstance : Module.Finite x.A (Fin n → Fin n → DD x.A k.g))
  haveI : Finite (IsLocalRing.ResidueField x.A) :=
    Finite.of_equiv x.K (PowerSeries.residueFieldOfPowerSeries).toEquiv.symm
  have hRes : Nat.card (IsLocalRing.ResidueField x.A) = Nat.card x.K :=
    Nat.card_congr (PowerSeries.residueFieldOfPowerSeries).toEquiv
  let f : Option (Option S) → (Matrix (Fin n) (Fin n) (DD x.A k.g) →ₗ[x.A] Matrix (Fin n) (Fin n) (DD x.A k.g)) :=
    fun o => match o with
    | none => fixBd_p n x.a (fixBd_q x.A x.A k.g b₁ b₂ b₃ b₄) (fixBd_q x.A x.A k.g c₁ c₂ c₃ c₄)
    | some none => if tr then (Matrix.transposeLinearEquiv (Fin n) (Fin n) x.A (DD x.A k.g)).toLinearMap + LinearMap.id else 0
    | some (some s) => e s • ((LinearMap.mulLeft x.A (P s)).comp (LinearMap.mulRight x.A (Q s))) - LinearMap.id
  obtain ⟨C, hC⟩ := fixBd_abs (A := x.A) (E := Matrix (Fin n) (Fin n) (DD x.A k.g)) f
  refine ⟨C, ?_⟩
  have hT0 : LinearMap.ker (f (some none)) = (if tr then LinearMap.ker ((Matrix.transposeLinearEquiv (Fin n) (Fin n) x.A (DD x.A k.g)).toLinearMap + LinearMap.id) else ⊤) := by
    show LinearMap.ker (if tr then _ else 0) = _
    split_ifs <;> simp
  have hK : (⨅ o, LinearMap.ker (f o)) = (V ⊓ (if tr then LinearMap.ker ((Matrix.transposeLinearEquiv (Fin n) (Fin n) x.A (DD x.A k.g)).toLinearMap + LinearMap.id) else ⊤) ⊓ ⨅ s, LinearMap.ker (e s • ((LinearMap.mulLeft x.A (P s)).comp (LinearMap.mulRight x.A (Q s))) - LinearMap.id) : Submodule x.A (Matrix (Fin n) (Fin n) (DD x.A k.g))) := by
    ext Z
    have e0 : Z ∈ LinearMap.ker (f none) ↔ Z ∈ V := by
      rw [LinearMap.mem_ker, hV]
      exact fixBd_p_zero n x.a b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ Z
    have e1 : Z ∈ LinearMap.ker (f (some none)) ↔ Z ∈ (if tr then LinearMap.ker ((Matrix.transposeLinearEquiv (Fin n) (Fin n) x.A (DD x.A k.g)).toLinearMap + LinearMap.id) else ⊤) := by
      rw [hT0]
    rw [Submodule.mem_iInf, Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_iInf]
    constructor
    · intro hZ
      exact ⟨⟨e0.1 (hZ none), e1.1 (hZ (some none))⟩, fun s => hZ (some (some s))⟩
    · rintro ⟨⟨h0, h1⟩, h2⟩ o
      rcases o with _ | _ | s
      · exact e0.2 h0
      · exact e1.2 h1
      · exact h2 s
  rw [← hK, ← hRes]
  intro m
  let r : Matrix (Fin n) (Fin n) (DD x.A k.g) →ₗ[x.A] Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) :=
    (x.redD k.g m).mapMatrix.toLinearMap
  have hker : LinearMap.ker r = IsLocalRing.maximalIdeal x.A ^ m • (⊤ : Submodule x.A (Matrix (Fin n) (Fin n) (DD x.A k.g))) := by
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
    ext Z
    rw [LinearMap.mem_ker, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · intro hZ
      have h1 : ∀ i j, ∃ z, (PowerSeries.X : x.A) ^ m • z = Z i j := fun i j =>
        (fixBd_ker ((PowerSeries.X : x.A) ^ m) k.g (Z i j)).1 (congrFun (congrFun hZ i) j)
      choose W hW using h1
      exact ⟨Matrix.of W, Submodule.mem_top, Matrix.ext fun i j => hW i j⟩
    · rintro ⟨W, -, rfl⟩
      refine Matrix.ext fun i j => ?_
      exact (fixBd_ker ((PowerSeries.X : x.A) ^ m) k.g _).2 ⟨W i j, rfl⟩
  apply hC m _ r _ hker
  intro Y hY
  have hl : ∀ i j, ∃ z, x.redD k.g m z = Y i j := fun i j => fixBd_surj _ k.g (Y i j)
  choose Z0 hZ0 using hl
  have hZY : r (Matrix.of Z0) = Y := Matrix.ext fun i j => hZ0 i j
  refine ⟨Matrix.of Z0, hZY, ?_⟩
  intro o
  rcases o with _ | _ | s
  · have hp : r (fixBd_p n x.a (fixBd_q x.A x.A k.g b₁ b₂ b₃ b₄) (fixBd_q x.A x.A k.g c₁ c₂ c₃ c₄) (Matrix.of Z0)) =
        fixBd_p n x.a (fixBd_q x.A (x.Am m) k.g b₁ b₂ b₃ b₄) (fixBd_q x.A (x.Am m) k.g c₁ c₂ c₃ c₄) Y := by
      rw [← hZY]
      refine Matrix.ext fun i j => ?_
      show x.redD k.g m (if _ then _ else _) = if _ then _ else _
      split_ifs
      · exact fixBd_q_map _ _ _ _ _ _
      · exact fixBd_q_map _ _ _ _ _ _
    show r (fixBd_p n x.a (fixBd_q x.A x.A k.g b₁ b₂ b₃ b₄) (fixBd_q x.A x.A k.g c₁ c₂ c₃ c₄) (Matrix.of Z0)) = 0
    rw [hp]
    exact (fixBd_p_zero n x.a b₁ b₂ b₃ b₄ c₁ c₂ c₃ c₄ Y).2 hY.1
  · show r ((if tr then (Matrix.transposeLinearEquiv (Fin n) (Fin n) x.A (DD x.A k.g)).toLinearMap + LinearMap.id else 0 :
        Matrix (Fin n) (Fin n) (DD x.A k.g) →ₗ[x.A] Matrix (Fin n) (Fin n) (DD x.A k.g)) (Matrix.of Z0)) = 0
    split_ifs with htr
    · have ht : r ((Matrix.transposeLinearEquiv (Fin n) (Fin n) x.A (DD x.A k.g)).toLinearMap (Matrix.of Z0)) = Yᵀ := by
        rw [← hZY]
        rfl
      rw [LinearMap.add_apply, map_add, LinearMap.id_apply, hZY, ht, hY.2.1 htr, neg_add_cancel]
    · simp
  · show r ((e s • ((LinearMap.mulLeft x.A (P s)).comp (LinearMap.mulRight x.A (Q s))) - LinearMap.id :
        Matrix (Fin n) (Fin n) (DD x.A k.g) →ₗ[x.A] Matrix (Fin n) (Fin n) (DD x.A k.g)) (Matrix.of Z0)) = 0
    have hm : ∀ M : Matrix (Fin n) (Fin n) (DD x.A k.g), (x.redD k.g m).mapMatrix M = M.map (fun y => ⟨algebraMap x.A (x.Am m) y.a, fun j => algebraMap x.A (x.Am m) (y.ep j), fun j => algebraMap x.A (x.Am m) (y.ep' j), algebraMap x.A (x.Am m) y.eta⟩) := fun M => rfl
    have hZY' : (x.redD k.g m).mapMatrix (Matrix.of Z0) = Y := hZY
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, LinearMap.id_apply]
    show (x.redD k.g m).mapMatrix (e s • (P s * (Matrix.of Z0 * Q s)) - Matrix.of Z0) = 0
    rw [map_sub, map_smul, map_mul, map_mul, hZY', hm (P s), hm (Q s), ← mul_assoc, hY.2.2 s, sub_self]
