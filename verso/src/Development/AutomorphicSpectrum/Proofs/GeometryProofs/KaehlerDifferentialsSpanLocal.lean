import Mathlib
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Kaehler

/- English proof (translation)
Set `_ : Module S M` to `Module.compHom M ψ`. Set `_ : Module ℚ M` to `Module.compHom M (algebraMap ℚ S)`. Establish `: IsScalarTower ℚ S M` using `⟨fun q a x => by`. Express the relevant statement in the definitionally equal form `ψ (q • a) • x = ψ (algebraMap ℚ S q) • (ψ a • x)`. Rewrite using `[Algebra.smul_def, map_mul, mul_smul]⟩`.

Establish `hsm : ∀ (a : S) (x : M), a • x = ψ a • x` using `fun _ _ => rfl`. Set `D : Derivation ℚ S M` to `Derivation.mk' D₀.toRatLinearMap (fun a b => by`. Simplify `leib a b)` using `[hsm]`. Establish `hD : ∀ a, D a = D₀ a` using `fun _ => rfl`. Set `L` to `D.liftKaehlerDifferential`.

Establish `hL : ∀ a, L (KaehlerDifferential.D ℚ S a) = D₀ a` using `fun a => by`. Simplify using `[L, hD]`. Establish `key : ∀ x : Ω[S⁄ℚ], L x ∈ Submodule.span B (Set.range fun i => D₀ (z i))`. Introduce `x`. Establish `hx : x ∈ Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i))`.

Rewrite using `[hz]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨i, rfl⟩` from `hy`.

Rewrite using `[hL]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Consider the case `zero => simp`. Consider the case `add y w _ _ hy hw => rw [map_add]`. Conclude with `add_mem hy hw`.

Consider the case `smul a y _ hy`. Rewrite using `[map_smul, hsm]`. Conclude with `Submodule.smul_mem _ _ hy`. Simplify `key (KaehlerDifferential.D ℚ S s)` using `[hL]`.
-/
theorem derivation_mem_span {S B M : Type} [CommRing S] [Algebra ℚ S] [CommRing B]
    [AddCommGroup M] [Module B M] (ψ : S →+* B) (D₀ : S →+ M)
    (leib : ∀ a b, D₀ (a * b) = ψ a • D₀ b + ψ b • D₀ a)
    {n : ℕ} (z : Fin n → S)
    (hz : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤) (s : S) :
    D₀ s ∈ Submodule.span B (Set.range fun i => D₀ (z i)) := by
  let _ : Module S M := Module.compHom M ψ
  let _ : Module ℚ M := Module.compHom M (algebraMap ℚ S)
  have : IsScalarTower ℚ S M := ⟨fun q a x => by
    change ψ (q • a) • x = ψ (algebraMap ℚ S q) • (ψ a • x)
    rw [Algebra.smul_def, map_mul, mul_smul]⟩
  have hsm : ∀ (a : S) (x : M), a • x = ψ a • x := fun _ _ => rfl
  let D : Derivation ℚ S M := Derivation.mk' D₀.toRatLinearMap (fun a b => by
    simpa [hsm] using leib a b)
  have hD : ∀ a, D a = D₀ a := fun _ => rfl
  let L := D.liftKaehlerDifferential
  have hL : ∀ a, L (KaehlerDifferential.D ℚ S a) = D₀ a := fun a => by
    simp [L, hD]
  have key : ∀ x : Ω[S⁄ℚ], L x ∈ Submodule.span B (Set.range fun i => D₀ (z i)) := by
    intro x
    have hx : x ∈ Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) := by
      rw [hz]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [hL]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add y w _ _ hy hw => rw [map_add]; exact add_mem hy hw
    | smul a y _ hy =>
      rw [map_smul, hsm]
      exact Submodule.smul_mem _ _ hy
  simpa [hL] using key (KaehlerDifferential.D ℚ S s)

/- English proof (translation)
Introduce `S B _ _ _ _ _ _ ψ φ hmem T hT n z hz`. Use `set m := IsLocalRing.maximalIdeal B with hm`. Use `set f : S → B := fun s => ψ s - algebraMap ℂ B (φ s) with hf`. Use `set J : Ideal B := Ideal.span (Set.range fun i => f (z i)) with hJ`. Establish `hJm : J ≤ m`.

Rewrite using `[hJ, Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hmem (z i)`. Set `D₀ : S →+ m.Cotangent` to `{ toFun := fun s => m.toCotangent ⟨f s, hmem s⟩ map_zero' := by`. Establish `: (⟨f 0, hmem 0⟩ : m) = 0` using `by ext; simp [hf]`.

Rewrite using `[this, map_zero]`. Use the proof step `map_add' := fun a b => by`. Rewrite using `[← map_add]`. Use `congr 1`. Use `ext`.

Simplify using `[hf]`. Use `ring }`. Establish `hD₀ : ∀ s, D₀ s = m.toCotangent ⟨f s, hmem s⟩` using `fun _ => rfl`. Establish `leib : ∀ a b, D₀ (a * b) = ψ a • D₀ b + ψ b • D₀ a`. Introduce `a b`.

Rewrite using `[hD₀, hD₀, hD₀, ← map_smul, ← map_smul, ← map_add, Ideal.toCotangent_eq]`. Establish `h2 : f a * f b ∈ m ^ 2`. Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul (hmem a) (hmem b)`. Establish `: ((⟨f (a * b), hmem (a * b)⟩ : m) : B) - ((ψ a • (⟨f b, hmem b⟩ : m) + ψ b • (⟨f a, hmem a⟩ : m) : m) : B) = -(f a * f b)`.

Simplify using `[hf]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `(m ^ 2).neg_mem h2`. Establish `hspan : ∀ s, D₀ s ∈ Submodule.span B (Set.range fun i => D₀ (z i))` using `derivation_mem_span ψ D₀ leib z hz`.

Set `Q : Submodule B m.Cotangent` to `Submodule.map m.toCotangent (Submodule.comap m.subtype J)`. Establish `hPQ : Submodule.span B (Set.range fun i => D₀ (z i)) ≤ Q`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨⟨f (z i), hmem (z i)⟩, Ideal.subset_span ⟨i, rfl⟩, rfl⟩`.

Establish `hfs : ∀ s, f s ∈ J ⊔ m • m`. Introduce `s`. Take `⟨y, hyJ, hy⟩` from `hPQ (hspan s)`. Establish `hy'` using `(Ideal.toCotangent_eq (I := m)).1 (hy.trans (hD₀ s))`. Establish `hsub : f s = (y : B) - ((y : B) - f s)` using `by ring`.

Rewrite using `[hsub]`. Use `Submodule.sub_mem _ (Submodule.mem_sup_left hyJ) (Submodule.mem_sup_right ?_)` and prove the remaining obligations. Simplify `hy'` using `[pow_two]`. Establish `hle : m ≤ J ⊔ m • m` using `by conv_lhs => rw [hT]`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨s, _, rfl⟩`. Conclude with `hfs s`. Apply `le_antisymm _ hJm` to reduce the goal to its premises. Conclude with `Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian m) (IsLocalRing.maximalIdeal_le_jacobson _) hle`.
-/
theorem maximalIdeal_eq_span_of_span_D :
    ∀ (S B : Type) [CommRing S] [Algebra ℚ S] [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [Algebra ℂ B] (ψ : S →+* B) (φ : S →+* ℂ),
    (∀ s, ψ s - algebraMap ℂ B (φ s) ∈ IsLocalRing.maximalIdeal B) →
    ∀ (T : Set S), IsLocalRing.maximalIdeal B = Ideal.span ((fun s => ψ s - algebraMap ℂ B (φ s)) '' T) →
    ∀ (n : ℕ) (z : Fin n → S),
    Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ →
    IsLocalRing.maximalIdeal B = Ideal.span (Set.range fun i => ψ (z i) - algebraMap ℂ B (φ (z i))) := by
  intro S B _ _ _ _ _ _ ψ φ hmem T hT n z hz
  set m := IsLocalRing.maximalIdeal B with hm
  set f : S → B := fun s => ψ s - algebraMap ℂ B (φ s) with hf
  set J : Ideal B := Ideal.span (Set.range fun i => f (z i)) with hJ
  have hJm : J ≤ m := by
    rw [hJ, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem (z i)
  let D₀ : S →+ m.Cotangent :=
    { toFun := fun s => m.toCotangent ⟨f s, hmem s⟩
      map_zero' := by
        have : (⟨f 0, hmem 0⟩ : m) = 0 := by ext; simp [hf]
        rw [this, map_zero]
      map_add' := fun a b => by
        rw [← map_add]
        congr 1
        ext
        simp [hf]
        ring }
  have hD₀ : ∀ s, D₀ s = m.toCotangent ⟨f s, hmem s⟩ := fun _ => rfl
  have leib : ∀ a b, D₀ (a * b) = ψ a • D₀ b + ψ b • D₀ a := by
    intro a b
    rw [hD₀, hD₀, hD₀, ← map_smul, ← map_smul, ← map_add, Ideal.toCotangent_eq]
    have h2 : f a * f b ∈ m ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul (hmem a) (hmem b)
    have : ((⟨f (a * b), hmem (a * b)⟩ : m) : B)
        - ((ψ a • (⟨f b, hmem b⟩ : m) + ψ b • (⟨f a, hmem a⟩ : m) : m) : B) = -(f a * f b) := by
      simp [hf]
      ring
    rw [this]
    exact (m ^ 2).neg_mem h2
  have hspan : ∀ s, D₀ s ∈ Submodule.span B (Set.range fun i => D₀ (z i)) :=
    derivation_mem_span ψ D₀ leib z hz
  let Q : Submodule B m.Cotangent := Submodule.map m.toCotangent (Submodule.comap m.subtype J)
  have hPQ : Submodule.span B (Set.range fun i => D₀ (z i)) ≤ Q := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨f (z i), hmem (z i)⟩, Ideal.subset_span ⟨i, rfl⟩, rfl⟩
  have hfs : ∀ s, f s ∈ J ⊔ m • m := by
    intro s
    obtain ⟨y, hyJ, hy⟩ := hPQ (hspan s)
    have hy' := (Ideal.toCotangent_eq (I := m)).1 (hy.trans (hD₀ s))
    have hsub : f s = (y : B) - ((y : B) - f s) := by ring
    rw [hsub]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left hyJ) (Submodule.mem_sup_right ?_)
    simpa [pow_two] using hy'
  have hle : m ≤ J ⊔ m • m := by
    conv_lhs => rw [hT]
    rw [Ideal.span_le]
    rintro _ ⟨s, _, rfl⟩
    exact hfs s
  apply le_antisymm _ hJm
  exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian m)
    (IsLocalRing.maximalIdeal_le_jacobson _) hle

end GlobalTheory.CompanionTheory.Kaehler
