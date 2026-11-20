import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.BndOps

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section
variable {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (t : A)
  (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R)
  (V : Submodule A (Matrix (Fin n) (Fin n) R))

end

/- English proof (translation)
Simplify using `only [W2, blkMat, ddPart, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at hM ⊢`. Introduce `i j`. Take `⟨h1, h2⟩` from `hM i j`. Use `⟨fun hij => ?_, fun hij => ?_⟩` and prove the remaining obligations. Take `⟨p, q, r, s⟩` from `h1 hij`.

Use `⟨fun hf => ?_, fun hf => ?_, fun hf => ?_, fun hf => ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.smul_apply, DD.mul_a, DD.C_a, p hf]`. Use function extensionality and compare the values at `k`. Simplify using `[Matrix.smul_apply, DD.mul_ep, DD.C_ep, DD.C_a, q hf]`. Use function extensionality and compare the values at `k`.

Simplify using `[Matrix.smul_apply, DD.mul_ep', DD.C_ep', DD.C_a, r hf]`. Simplify using `[Matrix.smul_apply, DD.mul_eta, DD.C_ep, DD.C_ep', DD.C_eta, DD.C_a, s hf]`. Take `⟨p, q, r, s⟩` from `h2 hij`. Use `⟨fun hf => ?_, fun hf => ?_, fun hf => ?_, fun hf => ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.smul_apply, DD.mul_a, DD.C_a, p hf]`.

Use function extensionality and compare the values at `k`. Simplify using `[Matrix.smul_apply, DD.mul_ep, DD.C_ep, DD.C_a, q hf]`. Use function extensionality and compare the values at `k`. Simplify using `[Matrix.smul_apply, DD.mul_ep', DD.C_ep', DD.C_a, r hf]`. Simplify using `[Matrix.smul_apply, DD.mul_eta, DD.C_ep, DD.C_ep', DD.C_eta, DD.C_a, s hf]`.
-/
private theorem C_smul_mem_w2 {n : ℕ} {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {e a : ℕ}
    (c : X) (M : Matrix (Fin n) (Fin n) (DD X e)) (hM : M ∈ W2 n A X e a) :
    (DD.C c : DD X e) • M ∈ W2 n A X e a := by
  simp only [W2, blkMat, ddPart, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq] at hM ⊢
  intro i j
  obtain ⟨h1, h2⟩ := hM i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · obtain ⟨p, q, r, s⟩ := h1 hij
    refine ⟨fun hf => ?_, fun hf => ?_, fun hf => ?_, fun hf => ?_⟩
    · simp [Matrix.smul_apply, DD.mul_a, DD.C_a, p hf]
    · funext k
      simp [Matrix.smul_apply, DD.mul_ep, DD.C_ep, DD.C_a, q hf]
    · funext k
      simp [Matrix.smul_apply, DD.mul_ep', DD.C_ep', DD.C_a, r hf]
    · simp [Matrix.smul_apply, DD.mul_eta, DD.C_ep, DD.C_ep', DD.C_eta, DD.C_a, s hf]
  · obtain ⟨p, q, r, s⟩ := h2 hij
    refine ⟨fun hf => ?_, fun hf => ?_, fun hf => ?_, fun hf => ?_⟩
    · simp [Matrix.smul_apply, DD.mul_a, DD.C_a, p hf]
    · funext k
      simp [Matrix.smul_apply, DD.mul_ep, DD.C_ep, DD.C_a, q hf]
    · funext k
      simp [Matrix.smul_apply, DD.mul_ep', DD.C_ep', DD.C_a, r hf]
    · simp [Matrix.smul_apply, DD.mul_eta, DD.C_ep, DD.C_ep', DD.C_eta, DD.C_a, s hf]

/- English proof (translation)
Take `⟨a1, b1, c1, e1, f1, g1⟩` from `h₁`. Take `⟨a2, b2, c2, e2, f2, g2⟩` from `h₂`. Use `⟨fun g => V.add_mem (hd₁ _ (a1 g)) (hd₂ _ (a2 g)), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j N`. Establish `k1` using `(b1 i j N).comp (fun q => Ideal.Quotient.mk _ d₁ * q)`.

Establish `k2` using `(b2 i j N).comp (fun q => Ideal.Quotient.mk _ d₂ * q)`. Use `k1.add k2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using `[Matrix.add_apply, Matrix.smul_apply, map_add, map_mul]`. Introduce `g g'`.

Simplify using `only [c1, c2, smul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul, Matrix.mul_add]`. Normalize the expressions using the abelian group laws. Introduce `g`. Simplify using `only [e1, e2, Matrix.transpose_add, Matrix.transpose_smul, smul_neg, neg_add]`. Introduce `u g hg`.

Simplify using `[f1 u g hg, f2 u g hg]`. Introduce `v`. Take `⟨Y1, hY1, L1⟩` from `g1 v`. Take `⟨Y2, hY2, L2⟩` from `g2 v`. Use `⟨d₁ • Y1 + d₂ • Y2, V.add_mem (hd₁ _ hY1) (hd₂ _ hY2), ?_⟩` and prove the remaining obligations.

Introduce `γ`. Take `⟨p1, q1⟩` from `L1 γ`. Take `⟨p2, q2⟩` from `L2 γ`. Establish `key : wi v * ((d₁ • z₁ (F.φ v γ) + d₂ • z₂ (F.φ v γ)) - dY F ρ (d₁ • Y1 + d₂ • Y2) (F.φ v γ)) * w v = d₁ • (wi v * (z₁ (F.φ v γ) - dY F ρ Y1 (F.φ v γ)) * w v) + d₂ • (wi v * (z₂ (F.φ v γ) - dY F ρ Y2 (F.φ v γ)) * w v)`. Simplify using `only [dY, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add]`.

Normalize the expressions using the abelian group laws. Use `⟨fun i j hij => ?_, fun hg i => ?_⟩` and prove the remaining obligations. Use `show (wi v * ((d₁ • z₁ (F.φ v γ) + d₂ • z₂ (F.φ v γ)) - dY F ρ (d₁ • Y1 + d₂ • Y2) (F.φ v γ)) * w v) i j = 0`. Rewrite using `[key]`. Simplify using `[Matrix.add_apply, Matrix.smul_apply, p1 i j hij, p2 i j hij]`.

Use `show (wi v * ((d₁ • z₁ (F.φ v γ) + d₂ • z₂ (F.φ v γ)) - dY F ρ (d₁ • Y1 + d₂ • Y2) (F.φ v γ)) * w v) i i = 0`. Rewrite using `[key]`. Simplify using `[Matrix.add_apply, Matrix.smul_apply, q1 hg i, q2 hg i]`.
-/
private theorem smul_add_smul_mem_selZ {l : ℕ} [Fact l.Prime] {n : ℕ} {A : Type} [CommRing A] (F : GFrame l)
    {R : Type} [CommRing R] [Algebra A R] (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R)
    (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R))
    (d₁ d₂ : R) (hd₁ : ∀ M ∈ V, d₁ • M ∈ V) (hd₂ : ∀ M ∈ V, d₂ • M ∈ V)
    (z₁ z₂ : F.G₀ → Matrix (Fin n) (Fin n) R) (h₁ : z₁ ∈ SelZ F t ρ w wi V) (h₂ : z₂ ∈ SelZ F t ρ w wi V) :
    (fun g => d₁ • z₁ g + d₂ • z₂ g) ∈ SelZ F t ρ w wi V := by
  obtain ⟨a1, b1, c1, e1, f1, g1⟩ := h₁
  obtain ⟨a2, b2, c2, e2, f2, g2⟩ := h₂
  refine ⟨fun g => V.add_mem (hd₁ _ (a1 g)) (hd₂ _ (a2 g)), ?_, ?_, ?_, ?_, ?_⟩
  · intro i j N
    have k1 := (b1 i j N).comp (fun q => Ideal.Quotient.mk _ d₁ * q)
    have k2 := (b2 i j N).comp (fun q => Ideal.Quotient.mk _ d₂ * q)
    convert k1.add k2 using 1
    funext g
    simp [Matrix.add_apply, Matrix.smul_apply, map_add, map_mul]
  · intro g g'
    simp only [c1, c2, smul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul, Matrix.mul_add]
    abel
  · intro g
    simp only [e1, e2, Matrix.transpose_add, Matrix.transpose_smul, smul_neg, neg_add]
  · intro u g hg
    simp [f1 u g hg, f2 u g hg]
  · intro v
    obtain ⟨Y1, hY1, L1⟩ := g1 v
    obtain ⟨Y2, hY2, L2⟩ := g2 v
    refine ⟨d₁ • Y1 + d₂ • Y2, V.add_mem (hd₁ _ hY1) (hd₂ _ hY2), ?_⟩
    intro γ
    obtain ⟨p1, q1⟩ := L1 γ
    obtain ⟨p2, q2⟩ := L2 γ
    have key : wi v * ((d₁ • z₁ (F.φ v γ) + d₂ • z₂ (F.φ v γ)) - dY F ρ (d₁ • Y1 + d₂ • Y2) (F.φ v γ)) * w v
        = d₁ • (wi v * (z₁ (F.φ v γ) - dY F ρ Y1 (F.φ v γ)) * w v)
          + d₂ • (wi v * (z₂ (F.φ v γ) - dY F ρ Y2 (F.φ v γ)) * w v) := by
      simp only [dY, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.smul_mul, smul_sub, smul_add]
      abel
    refine ⟨fun i j hij => ?_, fun hg i => ?_⟩
    · show (wi v * ((d₁ • z₁ (F.φ v γ) + d₂ • z₂ (F.φ v γ)) - dY F ρ (d₁ • Y1 + d₂ • Y2) (F.φ v γ)) * w v) i j = 0
      rw [key]
      simp [Matrix.add_apply, Matrix.smul_apply, p1 i j hij, p2 i j hij]
    · show (wi v * ((d₁ • z₁ (F.φ v γ) + d₂ • z₂ (F.φ v γ)) - dY F ρ (d₁ • Y1 + d₂ • Y2) (F.φ v γ)) * w v) i i = 0
      rw [key]
      simp [Matrix.add_apply, Matrix.smul_apply, q1 hg i, q2 hg i]

/- English proof (translation)
Use `⟨fun g => V.zero_mem, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j N`. Simplify using `only [Pi.zero_apply, Matrix.zero_apply, map_zero]`. Conclude with `IsLocallyConstant.const 0`. Introduce `g g'`.

Simplify using the standard rewrite rules. Introduce `g`. Simplify using the standard rewrite rules. Introduce `u g hg`. Both sides reduce to the same expression.

Introduce `v`. Apply the tactic sequence `refine ⟨0, V.zero_mem, fun γ => ⟨fun i j hij => ?_, fun hg i => ?_⟩⟩ <;> simp [dY]`.
-/
private theorem zero_mem_selZ {l : ℕ} [Fact l.Prime] {n : ℕ} {A : Type} [CommRing A] (F : GFrame l)
    {R : Type} [CommRing R] [Algebra A R] (t : A) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R)
    (w wi : F.Vl → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R)) :
    (0 : F.G₀ → Matrix (Fin n) (Fin n) R) ∈ SelZ F t ρ w wi V := by
  refine ⟨fun g => V.zero_mem, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j N
    simp only [Pi.zero_apply, Matrix.zero_apply, map_zero]
    exact IsLocallyConstant.const 0
  · intro g g'
    simp
  · intro g
    simp
  · intro u g hg
    rfl
  · intro v
    refine ⟨0, V.zero_mem, fun γ => ⟨fun i j hij => ?_, fun hg i => ?_⟩⟩ <;> simp [dY]

/- English proof (translation)
Take `⟨hc, hop, -⟩` from `bndOps K G`. Conclude with `(hop _ _ (hop _ _ (hc c₁) h1).2.1 (hop _ _ (hc c₂) h2).2.1).1`.
-/
private theorem bndF_mul_add_mul (K G : Type) [Field K] [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (c₁ c₂ : FractionRing (PowerSeries K)) (φ ψ : G → FractionRing (PowerSeries K))
    (h1 : BndF (PowerSeries.X : PowerSeries K) φ) (h2 : BndF (PowerSeries.X : PowerSeries K) ψ) :
    BndF (PowerSeries.X : PowerSeries K) (fun g => c₁ * φ g + c₂ * ψ g) := by
  obtain ⟨hc, hop, -⟩ := bndOps K G
  exact (hop _ _ (hop _ _ (hc c₁) h1).2.1 (hop _ _ (hc c₂) h2).2.1).1

/- English proof (translation)
Introduce `i j`. Take `⟨a1, b1, p1, e1⟩` from `h1 i j`. Take `⟨a2, b2, p2, e2⟩` from `h2 i j`. Use `⟨?_, fun k => ?_, fun k => ?_, ?_⟩` and prove the remaining obligations. Simplify `bndF_mul_add_mul K G c₁ c₂ _ _ a1 a2` using `[Matrix.add_apply, Matrix.smul_apply, DD.add_a, DD.mul_a, DD.C_a]`.

Simplify `bndF_mul_add_mul K G c₁ c₂ _ _ (b1 k) (b2 k)` using `[Matrix.add_apply, Matrix.smul_apply, DD.add_ep, DD.mul_ep, DD.C_a, DD.C_ep]`. Simplify `bndF_mul_add_mul K G c₁ c₂ _ _ (p1 k) (p2 k)` using `[Matrix.add_apply, Matrix.smul_apply, DD.add_ep', DD.mul_ep', DD.C_a, DD.C_ep']`. Simplify `bndF_mul_add_mul K G c₁ c₂ _ _ e1 e2` using `[Matrix.add_apply, Matrix.smul_apply, DD.add_eta, DD.mul_eta, DD.C_a, DD.C_ep, DD.C_ep', DD.C_eta]`.
-/
private theorem bndD_C_smul_add_C_smul {K G : Type} [Field K] [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {n e : ℕ} (c₁ c₂ : FractionRing (PowerSeries K))
    (Ψ₁ Ψ₂ : G → Matrix (Fin n) (Fin n) (DD (FractionRing (PowerSeries K)) e))
    (h1 : BndD (PowerSeries.X : PowerSeries K) Ψ₁) (h2 : BndD (PowerSeries.X : PowerSeries K) Ψ₂) :
    BndD (PowerSeries.X : PowerSeries K)
      (fun g => (DD.C c₁ : DD (FractionRing (PowerSeries K)) e) • Ψ₁ g + (DD.C c₂ : DD _ e) • Ψ₂ g) := by
  intro i j
  obtain ⟨a1, b1, p1, e1⟩ := h1 i j
  obtain ⟨a2, b2, p2, e2⟩ := h2 i j
  refine ⟨?_, fun k => ?_, fun k => ?_, ?_⟩
  · simpa [Matrix.add_apply, Matrix.smul_apply, DD.add_a, DD.mul_a, DD.C_a] using
      bndF_mul_add_mul K G c₁ c₂ _ _ a1 a2
  · simpa [Matrix.add_apply, Matrix.smul_apply, DD.add_ep, DD.mul_ep, DD.C_a, DD.C_ep] using
      bndF_mul_add_mul K G c₁ c₂ _ _ (b1 k) (b2 k)
  · simpa [Matrix.add_apply, Matrix.smul_apply, DD.add_ep', DD.mul_ep', DD.C_a, DD.C_ep'] using
      bndF_mul_add_mul K G c₁ c₂ _ _ (p1 k) (p2 k)
  · simpa [Matrix.add_apply, Matrix.smul_apply, DD.add_eta, DD.mul_eta, DD.C_a, DD.C_ep, DD.C_ep',
      DD.C_eta] using bndF_mul_add_mul K G c₁ c₂ _ _ e1 e2

/- English proof (translation)
Introduce `l _ L G G0 h n x k`. Establish `hV : ∀ (c : x.Fr), ∀ M ∈ W2 n x.A x.Fr k.g x.a, (DD.C c : DD x.Fr k.g) • M ∈ W2 n x.A x.Fr k.g x.a` using `fun c M hM => C_smul_mem_w2 c M hM`. Establish `lin : ∀ (c₁ c₂ : x.Fr) (z₁ z₂ : Fin k.g → G.G₀ → Matrix (Fin n) (Fin n) x.Fr), Lifts h k z₁ → Lifts h k z₂ → Lifts h k (fun j γ => c₁ • z₁ j γ + c₂ • z₂ j γ)`. Introduce and unpack `c₁ c₂ z₁ z₂ ⟨Ψ₁, m1, b1, e1⟩ ⟨Ψ₂, m2, b2, e2⟩`. Use `⟨fun γ => (DD.C c₁ : DD x.Fr k.g) • Ψ₁ γ + (DD.C c₂ : DD x.Fr k.g) • Ψ₂ γ, smul_add_smul_mem_selZ _ _ _ _ _ _ _ _ (hV c₁) (hV c₂) _ _ m1 m2, bndD_C_smul_add_C_smul c₁ c₂ _ _ b1 b2, ?_⟩` and prove the remaining obligations.

Introduce `j γ a b`. Simplify using `[Matrix.add_apply, Matrix.smul_apply, DD.add_ep', DD.mul_ep', DD.C_a, DD.C_ep', e1 j γ a b, e2 j γ a b]`. Use `⟨?_, fun z z' hz hz' => ?_, fun c z hz => ?_⟩` and prove the remaining obligations. Use `⟨0, zero_mem_selZ _ _ _ _ _ _, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j`.

Take `⟨hc, -⟩` from `bndOps x.K G.frame.G₀`. Use `⟨by simpa using hc 0, fun _ => by simpa using hc 0, fun _ => by simpa using hc 0, by simpa using hc 0⟩` and prove the remaining obligations. Introduce `j γ a b`. Simplify using the standard rewrite rules. Use `lin 1 1 z z' hz hz' using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `j γ`. Simplify using the standard rewrite rules. Use `lin c 0 z z hz hz using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j γ`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Pa.liftsSub :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), Lifts h k 0 ∧ (∀ z z' : Fin k.g → G.G₀ → Matrix (Fin n) (Fin n) x.Fr, Lifts h k z → Lifts h k z' → Lifts h k (z + z')) ∧ ∀ (c : x.Fr) (z : Fin k.g → G.G₀ → Matrix (Fin n) (Fin n) x.Fr), Lifts h k z → Lifts h k (c • z) := by
  intro l _ L G G0 h n x k
  have hV : ∀ (c : x.Fr), ∀ M ∈ W2 n x.A x.Fr k.g x.a, (DD.C c : DD x.Fr k.g) • M ∈ W2 n x.A x.Fr k.g x.a :=
    fun c M hM => C_smul_mem_w2 c M hM
  have lin : ∀ (c₁ c₂ : x.Fr) (z₁ z₂ : Fin k.g → G.G₀ → Matrix (Fin n) (Fin n) x.Fr),
      Lifts h k z₁ → Lifts h k z₂ → Lifts h k (fun j γ => c₁ • z₁ j γ + c₂ • z₂ j γ) := by
    rintro c₁ c₂ z₁ z₂ ⟨Ψ₁, m1, b1, e1⟩ ⟨Ψ₂, m2, b2, e2⟩
    refine ⟨fun γ => (DD.C c₁ : DD x.Fr k.g) • Ψ₁ γ + (DD.C c₂ : DD x.Fr k.g) • Ψ₂ γ,
      smul_add_smul_mem_selZ _ _ _ _ _ _ _ _ (hV c₁) (hV c₂) _ _ m1 m2, bndD_C_smul_add_C_smul c₁ c₂ _ _ b1 b2, ?_⟩
    intro j γ a b
    simp [Matrix.add_apply, Matrix.smul_apply, DD.add_ep', DD.mul_ep', DD.C_a, DD.C_ep', e1 j γ a b, e2 j γ a b]
  refine ⟨?_, fun z z' hz hz' => ?_, fun c z hz => ?_⟩
  · refine ⟨0, zero_mem_selZ _ _ _ _ _ _, ?_, ?_⟩
    · intro i j
      obtain ⟨hc, -⟩ := bndOps x.K G.frame.G₀
      refine ⟨by simpa using hc 0, fun _ => by simpa using hc 0, fun _ => by simpa using hc 0, by simpa using hc 0⟩
    · intro j γ a b
      simp
  · convert lin 1 1 z z' hz hz' using 1
    funext j γ
    simp
  · convert lin c 0 z z hz hz using 1
    funext j γ
    simp
