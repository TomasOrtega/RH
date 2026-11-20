import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.TopLeCopiesSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.RepEigCompl
open GlobalTheory.PRep Matrix UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
open scoped ComplexOrder

/- English proof (translation)
Set `T : Subgroup G` to `{ carrier := {g | ρ g (f n) = f n} mul_mem' := by`. Introduce `x y hx hy`. Simplify using `only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *`. Rewrite using `[hy, hx]`. Use the proof step `one_mem' := by simp`.

Use the proof step `inv_mem' := by`. Introduce `x hx`. Simplify using `only [Set.mem_setOf_eq] at *`. Use `conv_lhs => rw [← hx]`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`.

Simplify using `}`. Use `T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset ((hσ n).mem_nhds (by simp)) ?_)` and prove the remaining obligations. Introduce `g hg`. Establish `hg' : σ g n = n` using `hg`. Use `show ρ g (f n) = f n`.

Rewrite using `[← hf, hg']`.
-/
private theorem map_smooth {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] {N : Type}
    [AddCommGroup N] [Module k N] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : Representation k G V) (σ : Representation k G N) (hσ : IsSmooth σ) (f : N →ₗ[k] V)
    (hf : ∀ g v, f (σ g v) = ρ g (f v)) (n : N) : f n ∈ smoothPart ρ := by
  let T : Subgroup G :=
    { carrier := {g | ρ g (f n) = f n}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul]; simp }
  refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset ((hσ n).mem_nhds (by simp)) ?_)
  intro g hg
  have hg' : σ g n = n := hg
  show ρ g (f n) = f n
  rw [← hf, hg']

/- English proof (translation)
Introduce `v`. Establish `h : IsOpen {g : G | ρ g v.1 = v.1}` using `v.2`. Use `h using 3 with g` and compare the differences between its conclusion and the goal. Conclude with `Subtype.ext_iff`.
-/
private theorem smoothRep_smooth {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation k G V) : IsSmooth (smoothRep ρ) := by
  intro v
  have h : IsOpen {g : G | ρ g v.1 = v.1} := v.2
  convert h using 3 with g
  exact Subtype.ext_iff

/- English proof (translation)
Introduce `k G V _ _ _ _ N _ _ _ _ _ ρ σ hσ Y K χ hK hχ`. Establish `hE : (⨆ f : Into ρ Y σ, (eig σ K χ).map f.1) ≤ copies ρ Y σ ⊓ eig ρ K χ`. Use `iSup_le fun f => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨n, hn, rfl⟩`. Use `⟨Submodule.mem_iSup_of_mem f ⟨n, rfl⟩, fun h => ?_⟩` and prove the remaining obligations.

Rewrite using `[← f.2.1, hn h, map_smul]`. Use `le_antisymm ?_ hE` and prove the remaining obligations. Establish `hC` using `(repEigCompl σ K χ hσ hK hχ).1`. Establish `hD` using `(repEigCompl (smoothRep ρ) K χ (smoothRep_smooth ρ) hK hχ).1`. Establish `hT : ∀ f : Into ρ Y σ, ∀ n ∈ twKer σ K χ, f.1 n ∈ (twKer (smoothRep ρ) K χ).map (smoothPart ρ).subtype`.

Introduce `f`. Use `(Submodule.span_le (p := Submodule.comap f.1 ((twKer (smoothRep ρ) K χ).map (smoothPart ρ).subtype))).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, n, rfl⟩`. Use `⟨_, Submodule.subset_span ⟨x, ⟨f.1 n, map_smooth ρ σ hσ f.1 f.2.1 n⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_sub, map_smul, map_smul, f.2.1]`.

Both sides reduce to the same expression. Establish `hle : copies ρ Y σ ≤ (⨆ f : Into ρ Y σ, (eig σ K χ).map f.1) ⊔ (twKer (smoothRep ρ) K χ).map (smoothPart ρ).subtype`. Use `iSup_le fun f => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨n, rfl⟩`. Establish `hn : n ∈ eig σ K χ ⊔ twKer σ K χ` using `by rw [hC.sup_eq_top]; trivial`.

Take `⟨a, ha, t, ht, rfl⟩` from `Submodule.mem_sup.1 hn`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (Submodule.mem_iSup_of_mem f ⟨a, ha, rfl⟩) (hT f t ht)`. Introduce and unpack `v ⟨hv, hv'⟩`. Take `⟨e, he, _, ⟨t, ht, rfl⟩, rfl⟩` from `Submodule.mem_sup.1 (hle hv)`.

Establish `ht' : (t : V) ∈ eig ρ K χ`. Use `Submodule.sub_mem _ hv' (hE he).2` as an intermediate fact. Simplify using `using this`. Establish `ht'' : t ∈ eig (smoothRep ρ) K χ` using `fun h => Subtype.ext (ht' h)`. Establish `h0 : t = 0` using `(Submodule.disjoint_def.1 hD.disjoint) t ht'' ht`.

Substitute `h0` using the available equality. Simplify using `using he`.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.repEigSum :
    ∀ {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] {N : Type} [AddCommGroup N] [Module k N] [CharZero k] [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation k G V) (σ : Representation k G N), IsSmooth σ → ∀ (Y : Submodule k V) (K : Subgroup G) (χ : K →* kˣ), IsCompact (K : Set G) → IsOpen {x : K | χ x = 1} → copies ρ Y σ ⊓ eig ρ K χ = ⨆ f : Into ρ Y σ, (eig σ K χ).map f.1 := by
  intro k G V _ _ _ _ N _ _ _ _ _ ρ σ hσ Y K χ hK hχ
  have hE : (⨆ f : Into ρ Y σ, (eig σ K χ).map f.1) ≤ copies ρ Y σ ⊓ eig ρ K χ := by
    refine iSup_le fun f => ?_
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨Submodule.mem_iSup_of_mem f ⟨n, rfl⟩, fun h => ?_⟩
    rw [← f.2.1, hn h, map_smul]
  refine le_antisymm ?_ hE
  have hC := (repEigCompl σ K χ hσ hK hχ).1
  have hD := (repEigCompl (smoothRep ρ) K χ (smoothRep_smooth ρ) hK hχ).1
  have hT : ∀ f : Into ρ Y σ, ∀ n ∈ twKer σ K χ,
      f.1 n ∈ (twKer (smoothRep ρ) K χ).map (smoothPart ρ).subtype := by
    intro f
    refine (Submodule.span_le (p := Submodule.comap f.1 ((twKer (smoothRep ρ) K χ).map (smoothPart ρ).subtype))).2 ?_
    rintro _ ⟨x, n, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨x, ⟨f.1 n, map_smooth ρ σ hσ f.1 f.2.1 n⟩, rfl⟩, ?_⟩
    rw [map_sub, map_sub, map_smul, map_smul, f.2.1]
    rfl
  have hle : copies ρ Y σ ≤ (⨆ f : Into ρ Y σ, (eig σ K χ).map f.1) ⊔
      (twKer (smoothRep ρ) K χ).map (smoothPart ρ).subtype := by
    refine iSup_le fun f => ?_
    rintro _ ⟨n, rfl⟩
    have hn : n ∈ eig σ K χ ⊔ twKer σ K χ := by rw [hC.sup_eq_top]; trivial
    obtain ⟨a, ha, t, ht, rfl⟩ := Submodule.mem_sup.1 hn
    rw [map_add]
    exact Submodule.add_mem_sup (Submodule.mem_iSup_of_mem f ⟨a, ha, rfl⟩) (hT f t ht)
  rintro v ⟨hv, hv'⟩
  obtain ⟨e, he, _, ⟨t, ht, rfl⟩, rfl⟩ := Submodule.mem_sup.1 (hle hv)
  have ht' : (t : V) ∈ eig ρ K χ := by
    have := Submodule.sub_mem _ hv' (hE he).2
    simpa using this
  have ht'' : t ∈ eig (smoothRep ρ) K χ := fun h => Subtype.ext (ht' h)
  have h0 : t = 0 := (Submodule.disjoint_def.1 hD.disjoint) t ht'' ht
  subst h0
  simpa using he
