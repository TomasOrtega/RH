import ReciprocityTheory.DualLattices.CotangentSurjective

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.PullbackHopfOrder

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
theorem mem_augIdeal {X : Type} [AddCommGroup X] {M : Submodule R (X → C)} {f : X → C} :
    f ∈ augIdeal M ↔ f ∈ M ∧ f 0 = 0 := by
  exact Iff.rfl

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `h ⟨f, hf, f', hf', rfl⟩`. Use `show F (f * f') ∈ sqIdeal J`. Rewrite using `[hF]`. Conclude with `Submodule.subset_span ⟨_, hIJ f hf, _, hIJ f' hf', rfl⟩`.
-/
theorem sqIdeal_le {X Y : Type} (F : (X → C) →ₗ[R] (Y → C))
    (hF : ∀ f g, F (f * g) = F f * F g) {I : Submodule R (X → C)} {J : Submodule R (Y → C)}
    (hIJ : ∀ f ∈ I, F f ∈ J) : sqIdeal I ≤ (sqIdeal J).comap F := by
  refine Submodule.span_le.2 ?_
  rintro h ⟨f, hf, f', hf', rfl⟩
  show F (f * f') ∈ sqIdeal J
  rw [hF]
  exact Submodule.subset_span ⟨_, hIJ f hf, _, hIJ f' hf', rfl⟩

/- English proof (translation)
Use `Submodule.smul_le.2 fun r hr n _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, map_smul]`. Conclude with `Submodule.smul_mem_smul hr Submodule.mem_top`.
-/
theorem smulTop_le (q : ℕ) {a b : ℕ} (G : Matrix (Fin a) (Fin b) R) :
    (Ideal.span {(q : R)} • (⊤ : Submodule R (Fin b → R))) ≤
      (Ideal.span {(q : R)} • (⊤ : Submodule R (Fin a → R))).comap G.mulVecLin := by
  refine Submodule.smul_le.2 fun r hr n _ => ?_
  rw [Submodule.mem_comap, map_smul]
  exact Submodule.smul_mem_smul hr Submodule.mem_top

def mq (q : ℕ) {a b : ℕ} (G : Matrix (Fin a) (Fin b) R) :
    LieDualModP q R b →ₗ[R] LieDualModP q R a :=
  Submodule.mapQ _ _ G.mulVecLin (smulTop_le q G)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mq_mk (q : ℕ) {a b : ℕ} (G : Matrix (Fin a) (Fin b) R) (x : Fin b → R) :
    mq q G (Submodule.Quotient.mk x) = Submodule.Quotient.mk (G *ᵥ x) := rfl

def qPi (q d : ℕ) : LieDualModP q R d ≃ₗ[R] ((i : Fin d) → R ⧸ Ideal.span {(q : R)}) := by
  let πd : (Fin d → R) →ₗ[R] ((i : Fin d) → R ⧸ Ideal.span {(q : R)}) :=
    LinearMap.pi fun i => (Ideal.span {(q : R)}).mkQ ∘ₗ LinearMap.proj i
  have hπ : ∀ x i, πd x i = Submodule.Quotient.mk (x i) := fun _ _ => rfl
  have hsurj : Function.Surjective πd := by
    intro y
    choose x hx using fun i => Submodule.Quotient.mk_surjective _ (y i)
    exact ⟨x, funext fun i => by rw [hπ, hx]⟩
  have hker : Ideal.span {(q : R)} • (⊤ : Submodule R (Fin d → R)) = LinearMap.ker πd := by
    ext x
    rw [LinearMap.mem_ker]
    constructor
    · intro hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr n _
        funext i
        rw [hπ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, Pi.smul_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
      · intro x y hx hy
        rw [map_add, hx, hy, add_zero]
    · intro hx
      have : ∀ i, ∃ s, s * (q : R) = x i := fun i => by
        have := congrFun hx i
        rw [hπ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
        exact Ideal.mem_span_singleton'.1 this
      choose s hs using this
      have hx' : x = (q : R) • s := funext fun i => by
        rw [Pi.smul_apply, smul_eq_mul, mul_comm, hs]
      rw [hx']
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  exact (Submodule.quotEquivOfEq _ _ hker).trans (πd.quotKerEquivOfSurjective hsurj)

variable {X N : Type} [AddCommGroup X] [AddCommGroup N]

/- English proof (translation)
Establish `hM : P2 * F * P1 = 1`. Rewrite using `[← hF, ← Matrix.mul_assoc P2 P1 P2, h21, Matrix.one_mul, h21]`. Establish `hψI : ∀ f ∈ augIdeal A, LinearMap.funLeft R C ψ f ∈ augIdeal (A.map (LinearMap.funLeft R C ψ))`. Introduce `f hf`. Rewrite `hf`, the goal using `[mem_augIdeal]`.

Use `⟨Submodule.mem_map_of_mem hf.1, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.funLeft_apply, map_zero]`. Conclude with `hf.2`. Establish `hχI : ∀ g ∈ augIdeal (A.map (LinearMap.funLeft R C ψ)), LinearMap.funLeft R C χ g ∈ augIdeal A`. Introduce `g hg`.

Rewrite `hg`, the goal using `[mem_augIdeal]`. Take `⟨⟨f, hf, rfl⟩, h0⟩` from `hg`. Use `⟨hA f hf, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.funLeft_apply, map_zero]`. Conclude with `h0`.

Set `Φ0 : augIdeal (A.map (LinearMap.funLeft R C ψ)) →ₗ[R] augIdeal A` to `((LinearMap.funLeft R C χ).comp (augIdeal (A.map (LinearMap.funLeft R C ψ))).subtype).codRestrict (augIdeal A) (fun g => hχI g.1 g.2)`. Set `Φ : augIdeal (A.map (LinearMap.funLeft R C ψ)) →ₗ[R] LieDualModP q R d` to `mq q P2 ∘ₗ φ ∘ₗ Φ0`. Establish `hΦ : ∀ g, Φ g = mq q P2 (φ (Φ0 g))` using `fun _ => rfl`. Establish `hsurjΦ : Function.Surjective Φ`. Introduce `y`.

Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Take `⟨f, hf⟩` from `hsurj (Submodule.Quotient.mk (P1 *ᵥ w))`. Use `⟨⟨LinearMap.funLeft R C ψ f, hψI f f.2⟩, ?_⟩` and prove the remaining obligations. Establish `h1` using `hlin f (Φ0 ⟨LinearMap.funLeft R C ψ f, hψI f f.2⟩) (P1 *ᵥ w) (fun n => rfl) hf`. Rewrite using `[hΦ, h1, mq_mk, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]`.

Establish `hkerΦ : LinearMap.ker Φ = (sqIdeal (augIdeal (A.map (LinearMap.funLeft R C ψ)))).comap (augIdeal (A.map (LinearMap.funLeft R C ψ))).subtype`. Use extensionality with `u`. Rewrite using `[LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, hΦ]`. Prove the components needed by the constructor for the conclusion. Introduce `h0`.

Take `⟨l, hl⟩` from `Submodule.Quotient.mk_surjective _ (φ (Φ0 u))`. Establish `hfix` using `hlin (Φ0 u) (Φ0 u) l (fun n => by show (u : X → C) (χ n) = (u : X → C) (χ (ψ (χ n)))`. Rewrite using `[hχψ]) hl.symm`. Rewrite `h0` using `[← hl, mq_mk]`. Establish `hφ0 : φ (Φ0 u) = 0`.

Rewrite using `[hfix, ← hF, ← Matrix.mulVec_mulVec, show (Submodule.Quotient.mk (P1 *ᵥ (P2 *ᵥ l)) : LieDualModP q R g) = mq q P1 (Submodule.Quotient.mk (P2 *ᵥ l)) from rfl, h0, map_zero]`. Establish `hmem : ((Φ0 u : augIdeal A) : N → C) ∈ sqIdeal (augIdeal A)`. Use `LinearMap.mem_ker.2 hφ0` as an intermediate fact. Rewrite `this` using `[hker, Submodule.mem_comap]`. Conclude with `this`.

Use `Submodule.mem_comap.1 (sqIdeal_le (LinearMap.funLeft R C ψ) (fun _ _ => rfl) hψI hmem)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Use `show (u : X → C) x = (u : X → C) (χ (ψ x))`. Rewrite using `[hχψ]`.

Introduce `hu`. Establish `h1` using `Submodule.mem_comap.1 (sqIdeal_le (LinearMap.funLeft R C χ) (fun _ _ => rfl) hχI hu)`. Establish `hφ0 : φ (Φ0 u) = 0`. Rewrite using `[← LinearMap.mem_ker, hker, Submodule.mem_comap]`. Conclude with `h1`.

Rewrite using `[hφ0, map_zero]`. Conclude with `⟨(Submodule.quotEquivOfEq _ _ hkerΦ.symm).trans (Φ.quotKerEquivOfSurjective hsurjΦ)⟩`.
-/
theorem omega_pull (q : ℕ) {g d : ℕ} (ψ : X →+ N) (χ : N →+ X) (hχψ : ∀ x, χ (ψ x) = x)
    (A : Submodule R (N → C)) (hA : ∀ f ∈ A, (fun n => f (ψ (χ n))) ∈ A)
    (φ : augIdeal A →ₗ[R] LieDualModP q R g) (hsurj : Function.Surjective φ)
    (hker : LinearMap.ker φ = (sqIdeal (augIdeal A)).comap (augIdeal A).subtype)
    (F : Matrix (Fin g) (Fin g) R) (P1 : Matrix (Fin g) (Fin d) R) (P2 : Matrix (Fin d) (Fin g) R)
    (hF : P1 * P2 = F) (h21 : P2 * P1 = 1)
    (hlin : ∀ (f f' : augIdeal A) (l : Fin g → R),
      (∀ n, (f' : N → C) n = (f : N → C) (ψ (χ n))) →
      φ f = Submodule.Quotient.mk l → φ f' = Submodule.Quotient.mk (F *ᵥ l)) :
    Nonempty (OmAA (A.map (LinearMap.funLeft R C ψ)) ≃ₗ[R] LieDualModP q R d) := by
  classical
  have hM : P2 * F * P1 = 1 := by
    rw [← hF, ← Matrix.mul_assoc P2 P1 P2, h21, Matrix.one_mul, h21]
  have hψI : ∀ f ∈ augIdeal A,
      LinearMap.funLeft R C ψ f ∈ augIdeal (A.map (LinearMap.funLeft R C ψ)) := by
    intro f hf
    rw [mem_augIdeal] at hf ⊢
    refine ⟨Submodule.mem_map_of_mem hf.1, ?_⟩
    rw [LinearMap.funLeft_apply, map_zero]
    exact hf.2
  have hχI : ∀ g ∈ augIdeal (A.map (LinearMap.funLeft R C ψ)),
      LinearMap.funLeft R C χ g ∈ augIdeal A := by
    intro g hg
    rw [mem_augIdeal] at hg ⊢
    obtain ⟨⟨f, hf, rfl⟩, h0⟩ := hg
    refine ⟨hA f hf, ?_⟩
    rw [LinearMap.funLeft_apply, map_zero]
    exact h0
  let Φ0 : augIdeal (A.map (LinearMap.funLeft R C ψ)) →ₗ[R] augIdeal A :=
    ((LinearMap.funLeft R C χ).comp (augIdeal (A.map (LinearMap.funLeft R C ψ))).subtype).codRestrict
      (augIdeal A) (fun g => hχI g.1 g.2)
  let Φ : augIdeal (A.map (LinearMap.funLeft R C ψ)) →ₗ[R] LieDualModP q R d :=
    mq q P2 ∘ₗ φ ∘ₗ Φ0
  have hΦ : ∀ g, Φ g = mq q P2 (φ (Φ0 g)) := fun _ => rfl
  have hsurjΦ : Function.Surjective Φ := by
    intro y
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨f, hf⟩ := hsurj (Submodule.Quotient.mk (P1 *ᵥ w))
    refine ⟨⟨LinearMap.funLeft R C ψ f, hψI f f.2⟩, ?_⟩
    have h1 := hlin f (Φ0 ⟨LinearMap.funLeft R C ψ f, hψI f f.2⟩) (P1 *ᵥ w) (fun n => rfl) hf
    rw [hΦ, h1, mq_mk, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
  have hkerΦ : LinearMap.ker Φ = (sqIdeal (augIdeal (A.map (LinearMap.funLeft R C ψ)))).comap
      (augIdeal (A.map (LinearMap.funLeft R C ψ))).subtype := by
    ext u
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, hΦ]
    constructor
    · intro h0
      obtain ⟨l, hl⟩ := Submodule.Quotient.mk_surjective _ (φ (Φ0 u))
      have hfix := hlin (Φ0 u) (Φ0 u) l (fun n => by
        show (u : X → C) (χ n) = (u : X → C) (χ (ψ (χ n)))
        rw [hχψ]) hl.symm
      rw [← hl, mq_mk] at h0
      have hφ0 : φ (Φ0 u) = 0 := by
        rw [hfix, ← hF, ← Matrix.mulVec_mulVec,
          show (Submodule.Quotient.mk (P1 *ᵥ (P2 *ᵥ l)) : LieDualModP q R g) =
            mq q P1 (Submodule.Quotient.mk (P2 *ᵥ l)) from rfl, h0, map_zero]
      have hmem : ((Φ0 u : augIdeal A) : N → C) ∈ sqIdeal (augIdeal A) := by
        have := LinearMap.mem_ker.2 hφ0
        rw [hker, Submodule.mem_comap] at this
        exact this
      have := Submodule.mem_comap.1
        (sqIdeal_le (LinearMap.funLeft R C ψ) (fun _ _ => rfl) hψI hmem)
      convert this using 1
      funext x
      show (u : X → C) x = (u : X → C) (χ (ψ x))
      rw [hχψ]
    · intro hu
      have h1 := Submodule.mem_comap.1
        (sqIdeal_le (LinearMap.funLeft R C χ) (fun _ _ => rfl) hχI hu)
      have hφ0 : φ (Φ0 u) = 0 := by
        rw [← LinearMap.mem_ker, hker, Submodule.mem_comap]
        exact h1
      rw [hφ0, map_zero]
  exact ⟨(Submodule.quotEquivOfEq _ _ hkerΦ.symm).trans (Φ.quotKerEquivOfSurjective hsurjΦ)⟩

end ReciprocityTheory.PGsh.Up.PullbackHopfOrder
