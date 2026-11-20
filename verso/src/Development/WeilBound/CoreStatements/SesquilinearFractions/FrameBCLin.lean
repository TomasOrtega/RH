import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel

namespace PositivityTheory.Xgf.EigenspaceComposition

open GlobalTheory.CompanionTheory.Ar

variable {F F' : Type} [Field F] [Field F'] (f : F →+* F') {N : ℕ} {O : Type} [CommRing O]
  (ρ : O →+* Module.End F (Fin N → F)) (ρ' : O →+* Module.End F' (Fin N → F')) (τ : O →+* F)

/- English proof (translation)
Simplify using `[eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]`.
-/
theorem mem_eigSp {K : Type} [Field K] {ρ : O →+* Module.End K (Fin N → K)} {σ : O →+* K} (w : Fin N → K) :
    w ∈ eigSp ρ σ ↔ ∀ a, ρ a w = σ a • w := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
theorem comp_smul (c : F) (w : Fin N → F) : f ∘ (c • w) = f c • (f ∘ w) := by
  funext i; simp

/- English proof (translation)
Introduce `w w' h` and use `funext fun i => f.injective (congrFun h i)`.
-/
theorem comp_inj : Function.Injective fun w : Fin N → F => f ∘ w := fun w w' h =>
  funext fun i => f.injective (congrFun h i)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
theorem comp_add (w w' : Fin N → F) : f ∘ (w + w') = f ∘ w + f ∘ w' := by funext i; simp

variable {f ρ ρ' τ}

/- English proof (translation)
Rewrite using `[mem_eigSp, mem_eigSp]`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Rewrite using `[hρ, RingHom.comp_apply, ← comp_smul]`. Conclude with `(comp_inj f).eq_iff`.
-/
theorem mem_eigSp_comp (hρ : ∀ a u, ρ' a (f ∘ u) = f ∘ ρ a u) (w : Fin N → F) :
    f ∘ w ∈ eigSp ρ' (f.comp τ) ↔ w ∈ eigSp ρ τ := by
  rw [mem_eigSp, mem_eigSp]
  refine forall_congr' fun a => ?_
  rw [hρ, RingHom.comp_apply, ← comp_smul]
  exact (comp_inj f).eq_iff

/- English proof (translation)
Use `letI : Algebra F F' := f.toAlgebra`. Conclude with `linearIndependent_algebraMap_comp_iff`.
-/
theorem linIndep_comp {ι ι' : Type} [Finite ι'] (u : ι → ι' → F) :
    LinearIndependent F' (fun k => f ∘ u k) ↔ LinearIndependent F u := by
  letI : Algebra F F' := f.toAlgebra
  exact linearIndependent_algebraMap_comp_iff

/- English proof (translation)
Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨s, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨s, rfl⟩`. Consider the case `zero`.

Establish `: f ∘ (0 : Fin N → F) = 0` using `by funext i; simp`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [comp_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul c x _ hx => rw [comp_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem comp_mem_span {ι : Type} (g : ι → Fin N → F) (w : Fin N → F) (hw : w ∈ Submodule.span F (Set.range g)) :
    f ∘ w ∈ Submodule.span F' (Set.range fun s => f ∘ g s) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    exact Submodule.subset_span ⟨s, rfl⟩
  | zero =>
    have : f ∘ (0 : Fin N → F) = 0 := by funext i; simp
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [comp_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [comp_smul]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Establish `hbW : ∀ k, b k ∈ eigSp ρ τ` using `fun k => hsp ▸ Submodule.subset_span ⟨k, rfl⟩`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `(mem_eigSp_comp hρ (b k)).2 (hbW k)`.

Introduce `w' hw'`. Establish `hbρ : ∀ a k, ρ a (b k) = τ a • b k` using `fun a k => (mem_eigSp (b k)).1 (hbW k) a`. Choose the witnesses or unpack the hypotheses as in `⟨A0, hA0⟩ : ∃ A0 : Finset O, ∀ w, (∀ a ∈ A0, ρ a w = τ a • w) → w ∈ eigSp ρ τ := by`. Set `T : Set (Submodule F (Fin N → F))` to `{K | ∃ A : Finset O, K = ⨅ a ∈ A, LinearMap.ker (ρ a - τ a • LinearMap.id)}`. Take `⟨K, ⟨A, rfl⟩, hmin⟩` from `IsArtinian.set_has_minimal T ⟨_, ⟨∅, rfl⟩⟩`.

Use `⟨A, fun w hw => (mem_eigSp w).2 fun a => ?_⟩` and prove the remaining obligations. Establish `hle : (⨅ a' ∈ insert a A, LinearMap.ker (ρ a' - τ a' • LinearMap.id)) ≤ ⨅ a' ∈ A, LinearMap.ker (ρ a' - τ a' • LinearMap.id)` using `iInf_mono fun a' => iInf_mono' fun h => ⟨Finset.mem_insert_of_mem h, le_rfl⟩`. Establish `heq` using `(eq_of_le_of_not_lt hle (hmin _ ⟨insert a A, rfl⟩))`. Establish `hwK : w ∈ ⨅ a' ∈ A, LinearMap.ker (ρ a' - τ a' • LinearMap.id)`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`.

Conclude with `hw`. Rewrite `hwK` using `[← heq]`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hwK`. Conclude with `hwK a (Finset.mem_insert_self a A)`. Take `⟨C, hC⟩` from `Submodule.exists_isCompl (eigSp ρ τ)`.

Set `bc` to `Module.finBasis F C`. Set `c : Fin (Module.finrank F C) → Fin N → F` to `fun j => (bc j : Fin N → F)`. Set `g : Fin n ⊕ Fin (Module.finrank F C) → Fin N → F` to `Sum.elim b c`. Establish `gspan : Submodule.span F (Set.range g) = ⊤`. Rewrite using `[eq_top_iff, ← hC.sup_eq_top]`.

Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[← hsp]`. Conclude with `Submodule.span_mono fun _ ⟨k, hk⟩ => ⟨Sum.inl k, hk⟩`. Introduce `v hv`. Establish `hr` using `bc.sum_repr ⟨v, hv⟩`.

Establish `hv2 : v = ((∑ j, bc.repr ⟨v, hv⟩ j • bc j : C) : Fin N → F)` using `by rw [hr]`. Rewrite using `[hv2, Submodule.coe_sum]`. Conclude with `Submodule.sum_mem _ fun j _ => by`. Rewrite using `[Submodule.coe_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)`.

Establish `g'span : Submodule.span F' (Set.range fun s => f ∘ g s) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `v _`. Rewrite using `[pi_eq_sum_univ v]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Establish `e : (fun j => if i = j then (1 : F') else 0) = f ∘ (fun j => if i = j then (1 : F) else 0)`. Apply the tactic sequence `funext j; by_cases h : i = j <;> simp [h]`. Rewrite using `[e]`. Conclude with `comp_mem_span g _ (gspan ▸ Submodule.mem_top)`. Take `⟨z, hz⟩` from `(Submodule.mem_span_range_iff_exists_fun F').1 (g'span ▸ (Submodule.mem_top : w' ∈ ⊤))`.

Rewrite `hz` using `[Fintype.sum_sum_type]`. Simplify using `only [g, Sum.elim_inl, Sum.elim_inr] at hz`. Set `V : Fin (Module.finrank F C) → A0 × Fin N → F` to `fun j p => (ρ p.1 (c j) - τ p.1 • c j) p.2`. Establish `hV : LinearIndependent F V`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce `y hy j`. Establish `hmem : ∑ j, y j • c j ∈ eigSp ρ τ`. Use `hA0 _ fun a ha => ?_` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Use function extensionality and compare the values at `i`.

Use `congrFun hy (⟨a, ha⟩, i)` as an intermediate fact. Simplify using `only [V, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this`. Simplify using `only [map_sum, map_smul, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]`. Rewrite using `[← this, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hCm : ∑ j, y j • c j ∈ C` using `C.sum_mem fun j _ => C.smul_mem _ (bc j).2`. Establish `h0 : ∑ j, y j • c j = 0` using `(Submodule.disjoint_def.1 hC.disjoint) _ hmem hCm`. Establish `h1 : ∑ j, y j • bc j = 0` using `Subtype.ext (by simpa [c] using h0)`.

Conclude with `Fintype.linearIndependent_iff.1 bc.linearIndependent y h1 j`. Establish `hV'` using `(linIndep_comp (f := f) V).2 hV`. Establish `hL : ∀ a, ∑ j, z (Sum.inr j) • (f ∘ (ρ a (c j) - τ a • c j)) = 0`. Introduce `a`. Establish `e1 : ρ' a w' - f (τ a) • w' = 0` using `sub_eq_zero.2 ((mem_eigSp w').1 hw' a)`.

Rewrite `e1` using `[← hz]`. Simplify using `only [map_add, map_sum, map_smul, hρ, hbρ, comp_smul] at e1`. Establish `hs : ∀ x y : Fin N → F, f ∘ (x - y) = f ∘ x - f ∘ y` using `fun x y => by funext i; simp`. Simplify using `only [hs, comp_smul]`. Rewrite using `[← e1]`.

Simplify using `only [smul_add, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]`. Establish `hc1 : ∀ x, f (τ a) • z (Sum.inl x) • (f ∘ b x) = z (Sum.inl x) • f (τ a) • (f ∘ b x)` using `fun x => smul_comm _ _ _`. Establish `hc2 : ∀ x, f (τ a) • z (Sum.inr x) • (f ∘ c x) = z (Sum.inr x) • f (τ a) • (f ∘ c x)` using `fun x => smul_comm _ _ _`. Simplify using `only [hc1, hc2]`. Normalize the expressions using the abelian group laws.

Establish `hy : ∀ j, z (Sum.inr j) = 0`. Establish `hsum : ∑ j, z (Sum.inr j) • (f ∘ V j) = 0`. Use function extensionality and compare the values at `p`. Use `congrFun (hL p.1.1) p.2` as an intermediate fact. Simplify `this` using `[V, Finset.sum_apply]`.

Introduce `j`. Conclude with `Fintype.linearIndependent_iff.1 hV' _ hsum j`. Rewrite using `[← hz]`. Simplify using `only [hy, zero_smul, Finset.sum_const_zero, add_zero]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.
-/
theorem span_comp_eq (hρ : ∀ a u, ρ' a (f ∘ u) = f ∘ ρ a u) {n : ℕ} (b : Fin n → Fin N → F)
    (hli : LinearIndependent F b) (hsp : Submodule.span F (Set.range b) = eigSp ρ τ) :
    Submodule.span F' (Set.range fun k => f ∘ b k) = eigSp ρ' (f.comp τ) := by
  classical
  have hbW : ∀ k, b k ∈ eigSp ρ τ := fun k => hsp ▸ Submodule.subset_span ⟨k, rfl⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact (mem_eigSp_comp hρ (b k)).2 (hbW k)
  intro w' hw'
  have hbρ : ∀ a k, ρ a (b k) = τ a • b k := fun a k => (mem_eigSp (b k)).1 (hbW k) a

  obtain ⟨A0, hA0⟩ : ∃ A0 : Finset O, ∀ w, (∀ a ∈ A0, ρ a w = τ a • w) → w ∈ eigSp ρ τ := by
    let T : Set (Submodule F (Fin N → F)) :=
      {K | ∃ A : Finset O, K = ⨅ a ∈ A, LinearMap.ker (ρ a - τ a • LinearMap.id)}
    obtain ⟨K, ⟨A, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal T ⟨_, ⟨∅, rfl⟩⟩
    refine ⟨A, fun w hw => (mem_eigSp w).2 fun a => ?_⟩
    have hle : (⨅ a' ∈ insert a A, LinearMap.ker (ρ a' - τ a' • LinearMap.id)) ≤
        ⨅ a' ∈ A, LinearMap.ker (ρ a' - τ a' • LinearMap.id) :=
      iInf_mono fun a' => iInf_mono' fun h => ⟨Finset.mem_insert_of_mem h, le_rfl⟩
    have heq := (eq_of_le_of_not_lt hle (hmin _ ⟨insert a A, rfl⟩))
    have hwK : w ∈ ⨅ a' ∈ A, LinearMap.ker (ρ a' - τ a' • LinearMap.id) := by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero]
      exact hw
    rw [← heq] at hwK
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] at hwK
    exact hwK a (Finset.mem_insert_self a A)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (eigSp ρ τ)
  let bc := Module.finBasis F C
  let c : Fin (Module.finrank F C) → Fin N → F := fun j => (bc j : Fin N → F)
  let g : Fin n ⊕ Fin (Module.finrank F C) → Fin N → F := Sum.elim b c
  have gspan : Submodule.span F (Set.range g) = ⊤ := by
    rw [eq_top_iff, ← hC.sup_eq_top]
    refine sup_le ?_ ?_
    · rw [← hsp]
      exact Submodule.span_mono fun _ ⟨k, hk⟩ => ⟨Sum.inl k, hk⟩
    · intro v hv
      have hr := bc.sum_repr ⟨v, hv⟩
      have hv2 : v = ((∑ j, bc.repr ⟨v, hv⟩ j • bc j : C) : Fin N → F) := by rw [hr]
      rw [hv2, Submodule.coe_sum]
      exact Submodule.sum_mem _ fun j _ => by
        rw [Submodule.coe_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
  have g'span : Submodule.span F' (Set.range fun s => f ∘ g s) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [pi_eq_sum_univ v]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have e : (fun j => if i = j then (1 : F') else 0) = f ∘ (fun j => if i = j then (1 : F) else 0) := by
      funext j; by_cases h : i = j <;> simp [h]
    rw [e]
    exact comp_mem_span g _ (gspan ▸ Submodule.mem_top)
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun F').1 (g'span ▸ (Submodule.mem_top : w' ∈ ⊤))
  rw [Fintype.sum_sum_type] at hz
  simp only [g, Sum.elim_inl, Sum.elim_inr] at hz
  let V : Fin (Module.finrank F C) → A0 × Fin N → F := fun j p => (ρ p.1 (c j) - τ p.1 • c j) p.2
  have hV : LinearIndependent F V := by
    rw [Fintype.linearIndependent_iff]
    intro y hy j
    have hmem : ∑ j, y j • c j ∈ eigSp ρ τ := by
      refine hA0 _ fun a ha => ?_
      rw [← sub_eq_zero]
      funext i
      have := congrFun hy (⟨a, ha⟩, i)
      simp only [V, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      simp only [map_sum, map_smul, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hCm : ∑ j, y j • c j ∈ C := C.sum_mem fun j _ => C.smul_mem _ (bc j).2
    have h0 : ∑ j, y j • c j = 0 := (Submodule.disjoint_def.1 hC.disjoint) _ hmem hCm
    have h1 : ∑ j, y j • bc j = 0 := Subtype.ext (by simpa [c] using h0)
    exact Fintype.linearIndependent_iff.1 bc.linearIndependent y h1 j
  have hV' := (linIndep_comp (f := f) V).2 hV
  have hL : ∀ a, ∑ j, z (Sum.inr j) • (f ∘ (ρ a (c j) - τ a • c j)) = 0 := by
    intro a
    have e1 : ρ' a w' - f (τ a) • w' = 0 := sub_eq_zero.2 ((mem_eigSp w').1 hw' a)
    rw [← hz] at e1
    simp only [map_add, map_sum, map_smul, hρ, hbρ, comp_smul] at e1
    have hs : ∀ x y : Fin N → F, f ∘ (x - y) = f ∘ x - f ∘ y := fun x y => by funext i; simp
    simp only [hs, comp_smul]
    rw [← e1]
    simp only [smul_add, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
    have hc1 : ∀ x, f (τ a) • z (Sum.inl x) • (f ∘ b x) = z (Sum.inl x) • f (τ a) • (f ∘ b x) :=
      fun x => smul_comm _ _ _
    have hc2 : ∀ x, f (τ a) • z (Sum.inr x) • (f ∘ c x) = z (Sum.inr x) • f (τ a) • (f ∘ c x) :=
      fun x => smul_comm _ _ _
    simp only [hc1, hc2]
    abel
  have hy : ∀ j, z (Sum.inr j) = 0 := by
    have hsum : ∑ j, z (Sum.inr j) • (f ∘ V j) = 0 := by
      funext p
      have := congrFun (hL p.1.1) p.2
      simpa [V, Finset.sum_apply] using this
    intro j
    exact Fintype.linearIndependent_iff.1 hV' _ hsum j
  rw [← hz]
  simp only [hy, zero_smul, Finset.sum_const_zero, add_zero]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hli, hsp⟩`. Conclude with `⟨(linIndep_comp (ι' := Fin N) u).2 hli, span_comp_eq hρ u hli hsp⟩`. Introduce and unpack `⟨hli', hsp'⟩`. Establish `hli` using `(linIndep_comp (ι' := Fin N) u).1 hli'`.

Use `⟨hli, ?_⟩` and prove the remaining obligations. Establish `hmem : ∀ k, u k ∈ eigSp ρ τ` using `fun k => (mem_eigSp_comp hρ (u k)).1 (hsp' ▸ Submodule.subset_span ⟨k, rfl⟩)`. Establish `hle : Submodule.span F (Set.range u) ≤ eigSp ρ τ`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`.

Conclude with `hmem k`. Set `W` to `eigSp ρ τ`. Set `bW` to `Module.finBasis F W`. Set `b : Fin (Module.finrank F W) → Fin N → F` to `fun j => (bW j : Fin N → F)`. Establish `hbli : LinearIndependent F b` using `bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)`.

Establish `hbsp : Submodule.span F (Set.range b) = W`. Establish `: Set.range b = W.subtype '' Set.range bW` using `by rw [← Set.range_comp]; rfl`. Rewrite using `[this, Submodule.span_image, bW.span_eq, Submodule.map_top, Submodule.range_subtype]`. Establish `hW'` using `span_comp_eq hρ b hbli hbsp`. Establish `e1 : Module.finrank F' (eigSp ρ' (f.comp τ)) = n`.

Rewrite using `[← hsp', finrank_span_eq_card hli', Fintype.card_fin]`. Establish `e2 : Module.finrank F' (eigSp ρ' (f.comp τ)) = Module.finrank F W`. Rewrite using `[← hW', finrank_span_eq_card ((linIndep_comp (ι' := Fin N) b).2 hbli), Fintype.card_fin]`. Apply `Submodule.eq_of_le_of_finrank_eq hle` to reduce the goal to its premises. Rewrite using `[finrank_span_eq_card hli, Fintype.card_fin, ← e1, e2]`.
-/
theorem core (hρ : ∀ a u, ρ' a (f ∘ u) = f ∘ ρ a u) {n : ℕ} (u : Fin n → Fin N → F) :
    (LinearIndependent F u ∧ Submodule.span F (Set.range u) = eigSp ρ τ) ↔
      (LinearIndependent F' (fun k => f ∘ u k) ∧ Submodule.span F' (Set.range fun k => f ∘ u k) = eigSp ρ' (f.comp τ)) := by
  constructor
  · rintro ⟨hli, hsp⟩
    exact ⟨(linIndep_comp (ι' := Fin N) u).2 hli, span_comp_eq hρ u hli hsp⟩
  · rintro ⟨hli', hsp'⟩
    have hli := (linIndep_comp (ι' := Fin N) u).1 hli'
    refine ⟨hli, ?_⟩
    have hmem : ∀ k, u k ∈ eigSp ρ τ := fun k =>
      (mem_eigSp_comp hρ (u k)).1 (hsp' ▸ Submodule.subset_span ⟨k, rfl⟩)
    have hle : Submodule.span F (Set.range u) ≤ eigSp ρ τ := by
      rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩; exact hmem k

    let W := eigSp ρ τ
    let bW := Module.finBasis F W
    let b : Fin (Module.finrank F W) → Fin N → F := fun j => (bW j : Fin N → F)
    have hbli : LinearIndependent F b := bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    have hbsp : Submodule.span F (Set.range b) = W := by
      have : Set.range b = W.subtype '' Set.range bW := by rw [← Set.range_comp]; rfl
      rw [this, Submodule.span_image, bW.span_eq, Submodule.map_top, Submodule.range_subtype]
    have hW' := span_comp_eq hρ b hbli hbsp
    have e1 : Module.finrank F' (eigSp ρ' (f.comp τ)) = n := by
      rw [← hsp', finrank_span_eq_card hli', Fintype.card_fin]
    have e2 : Module.finrank F' (eigSp ρ' (f.comp τ)) = Module.finrank F W := by
      rw [← hW', finrank_span_eq_card ((linIndep_comp (ι' := Fin N) b).2 hbli), Fintype.card_fin]
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_span_eq_card hli, Fintype.card_fin, ← e1, e2]

end PositivityTheory.Xgf.EigenspaceComposition
