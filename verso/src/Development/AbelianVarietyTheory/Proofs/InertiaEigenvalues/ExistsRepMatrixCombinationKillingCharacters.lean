import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.MatCorner

variable {Γ A : Type} [Group Γ] [CommRing A] {r : ℕ}

def pairOf (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (g : Γ) :
    Matrix (Fin r) (Fin r) A × (ℕ → A) :=
  (mat ρ g, fun c => ((χ c g : Aˣ) : A))

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `[pairOf, mat]`. Use function extensionality and compare the values at `c`. Simplify using `[pairOf]`.
-/
theorem pairOf_mul (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (g h : Γ) :
    pairOf ρ χ (g * h) = pairOf ρ χ g * pairOf ρ χ h := by
  refine Prod.ext ?_ ?_
  · simp [pairOf, mat]
  · funext c
    simp [pairOf]

/- English proof (translation)
Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨h, rfl⟩` from `hy`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨g, rfl⟩` from `hx`. Rewrite using `[← pairOf_mul]`. Conclude with `Submodule.subset_span ⟨g * h, rfl⟩`. Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz`.

Rewrite using `[add_mul]`. Conclude with `Submodule.add_mem _ hx hz`. Consider the case `smul c x _ hx`. Rewrite using `[smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ c hx`.

Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz`. Rewrite using `[mul_add]`. Conclude with `Submodule.add_mem _ hy hz`. Consider the case `smul c y _ hy`.

Rewrite using `[mul_smul_comm]`. Conclude with `Submodule.smul_mem _ c hy`.
-/
theorem mul_mem_span (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ))
    {a b : Matrix (Fin r) (Fin r) A × (ℕ → A)}
    (ha : a ∈ Submodule.span A (Set.range (pairOf ρ χ)))
    (hb : b ∈ Submodule.span A (Set.range (pairOf ρ χ))) :
    a * b ∈ Submodule.span A (Set.range (pairOf ρ χ)) := by
  induction hb using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, rfl⟩ := hy
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      rw [← pairOf_mul]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero => simp
    | add x z _ _ hx hz =>
      rw [add_mul]
      exact Submodule.add_mem _ hx hz
    | smul c x _ hx =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ c hx
  | zero => simp
  | add y z _ _ hy hz =>
    rw [mul_add]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ c hy

/- English proof (translation)
Establish `hfst : (LinearMap.fst A (Matrix (Fin r) (Fin r) A) (ℕ → A)) ∘ pairOf ρ χ = mat ρ`. Use function extensionality and compare the values at `g`. Both sides reduce to the same expression. Establish `hP : P ∈ (Submodule.span A (Set.range (pairOf ρ χ))).map (LinearMap.fst A (Matrix (Fin r) (Fin r) A) (ℕ → A))`. Rewrite using `[Submodule.map_span, ← Set.range_comp, hfst, hs]`.

Conclude with `Submodule.mem_top`. Take `⟨x, hx, rfl⟩` from `hP`. Conclude with `⟨x.2, by simpa using hx⟩`.
-/
theorem exists_lift (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ))
    (hs : Submodule.span A (Set.range (mat ρ)) = ⊤) (P : Matrix (Fin r) (Fin r) A) :
    ∃ v, (P, v) ∈ Submodule.span A (Set.range (pairOf ρ χ)) := by
  have hfst : (LinearMap.fst A (Matrix (Fin r) (Fin r) A) (ℕ → A)) ∘ pairOf ρ χ = mat ρ := by
    funext g
    rfl
  have hP : P ∈ (Submodule.span A (Set.range (pairOf ρ χ))).map
      (LinearMap.fst A (Matrix (Fin r) (Fin r) A) (ℕ → A)) := by
    rw [Submodule.map_span, ← Set.range_comp, hfst, hs]
    exact Submodule.mem_top
  obtain ⟨x, hx, rfl⟩ := hP
  exact ⟨x.2, by simpa using hx⟩

/- English proof (translation)
Use `set I := Submodule.span A (Set.range (pairOf ρ χ)) with hI`. Establish `sand : ∀ M X Y : Matrix (Fin r) (Fin r) A, (M, (0 : ℕ → A)) ∈ I → (X * M * Y, (0 : ℕ → A)) ∈ I`. Introduce `M X Y hM`. Take `⟨v, hv⟩` from `exists_lift ρ χ hs X`. Take `⟨w, hw⟩` from `exists_lift ρ χ hs Y`.

Establish `hXMY` using `mul_mem_span ρ χ (mul_mem_span ρ χ hv hM) hw`. Simplify using `using hXMY`. Take `⟨i0, i1, h01⟩ : ∃ i0 i1 : Fin r, i0 ≠ i1` from `⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩`. Establish `hE : (Matrix.single i0 i1 (1 : A), (0 : ℕ → A)) ∈ I`. Take `⟨v, hv⟩` from `exists_lift ρ χ hs (Matrix.single i0 i0 1)`.

Take `⟨w, hw⟩` from `exists_lift ρ χ hs (Matrix.single i0 i1 1)`. Establish `hc` using `I.sub_mem (mul_mem_span ρ χ hv hw) (mul_mem_span ρ χ hw hv)`. Establish `hz : Matrix.single i0 i1 (1 : A) * Matrix.single i0 i0 1 = 0` using `Matrix.single_mul_single_of_ne (1 : A) i0 i1 i0 h01.symm 1`. Simplify `hc` using `[hz, mul_comm w v]`. Establish `key : ∀ (i j : Fin r) (c : A), (Matrix.single i j c, (0 : ℕ → A)) ∈ I`.

Introduce `i j c`. Establish `hij` using `sand _ (Matrix.single i i0 c) (Matrix.single i1 j 1) hE`. Simplify using `using hij`. Set `J` to `I.comap (LinearMap.inl A (Matrix (Fin r) (Fin r) A) (ℕ → A))`. Establish `hPJ : P ∈ J`.

Rewrite using `[Matrix.matrix_eq_sum_single P]`. Conclude with `J.sum_mem fun i _ => J.sum_mem fun j _ => key i j (P i j)`. Conclude with `hPJ`.
-/
theorem pair_zero_mem (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (hr : 2 ≤ r)
    (hs : Submodule.span A (Set.range (mat ρ)) = ⊤) (P : Matrix (Fin r) (Fin r) A) :
    (P, (0 : ℕ → A)) ∈ Submodule.span A (Set.range (pairOf ρ χ)) := by
  set I := Submodule.span A (Set.range (pairOf ρ χ)) with hI

  have sand : ∀ M X Y : Matrix (Fin r) (Fin r) A, (M, (0 : ℕ → A)) ∈ I →
      (X * M * Y, (0 : ℕ → A)) ∈ I := by
    intro M X Y hM
    obtain ⟨v, hv⟩ := exists_lift ρ χ hs X
    obtain ⟨w, hw⟩ := exists_lift ρ χ hs Y
    have hXMY := mul_mem_span ρ χ (mul_mem_span ρ χ hv hM) hw
    simpa using hXMY
  obtain ⟨i0, i1, h01⟩ : ∃ i0 i1 : Fin r, i0 ≠ i1 :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩

  have hE : (Matrix.single i0 i1 (1 : A), (0 : ℕ → A)) ∈ I := by
    obtain ⟨v, hv⟩ := exists_lift ρ χ hs (Matrix.single i0 i0 1)
    obtain ⟨w, hw⟩ := exists_lift ρ χ hs (Matrix.single i0 i1 1)
    have hc := I.sub_mem (mul_mem_span ρ χ hv hw) (mul_mem_span ρ χ hw hv)
    have hz : Matrix.single i0 i1 (1 : A) * Matrix.single i0 i0 1 = 0 :=
      Matrix.single_mul_single_of_ne (1 : A) i0 i1 i0 h01.symm 1
    simpa [hz, mul_comm w v] using hc

  have key : ∀ (i j : Fin r) (c : A), (Matrix.single i j c, (0 : ℕ → A)) ∈ I := by
    intro i j c
    have hij := sand _ (Matrix.single i i0 c) (Matrix.single i1 j 1) hE
    simpa using hij
  let J := I.comap (LinearMap.inl A (Matrix (Fin r) (Fin r) A) (ℕ → A))
  have hPJ : P ∈ J := by
    rw [Matrix.matrix_eq_sum_single P]
    exact J.sum_mem fun i _ => J.sum_mem fun j _ => key i j (P i j)
  exact hPJ

/- English proof (translation)
Introduce `Γ A _ _ r ρ χ hr hs P`. Take `⟨m, f, g, hg⟩` from `Submodule.mem_span_set'.mp (pair_zero_mem ρ χ hr hs P)`. Use `choose h hh using fun k => Set.mem_range.mp (g k).2`. Establish `hsum : ∑ k, f k • pairOf ρ χ (h k) = (P, 0)` using `by simpa [hh] using hg`. Use `⟨m, f, h, ?_, fun c => ?_⟩` and prove the remaining obligations.

Establish `h1` using `congrArg Prod.fst hsum`. Simplify `h1` using `[Prod.fst_sum, pairOf]`. Establish `h2` using `congrFun (congrArg Prod.snd hsum) c`. Simplify `h2` using `[Prod.snd_sum, Finset.sum_apply, pairOf]`.
-/
theorem exists_comb_kills_chars :
    ∀ {Γ A : Type} [Group Γ] [CommRing A] {r : ℕ} (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)), 2 ≤ r →
      Submodule.span A (Set.range (mat ρ)) = ⊤ → ∀ P : Matrix (Fin r) (Fin r) A,
      ∃ (m : ℕ) (f : Fin m → A) (h : Fin m → Γ), ∑ k, f k • mat ρ (h k) = P ∧
        ∀ c : ℕ, ∑ k, f k * ((χ c (h k) : Aˣ) : A) = 0 := by
  intro Γ A _ _ r ρ χ hr hs P
  obtain ⟨m, f, g, hg⟩ := Submodule.mem_span_set'.mp (pair_zero_mem ρ χ hr hs P)
  choose h hh using fun k => Set.mem_range.mp (g k).2
  have hsum : ∑ k, f k • pairOf ρ χ (h k) = (P, 0) := by simpa [hh] using hg
  refine ⟨m, f, h, ?_, fun c => ?_⟩
  · have h1 := congrArg Prod.fst hsum
    simpa [Prod.fst_sum, pairOf] using h1
  · have h2 := congrFun (congrArg Prod.snd hsum) c
    simpa [Prod.snd_sum, Finset.sum_apply, pairOf] using h2

end GlobalTheory.MatCorner
