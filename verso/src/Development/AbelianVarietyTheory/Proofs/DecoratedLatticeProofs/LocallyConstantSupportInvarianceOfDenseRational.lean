import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge

namespace GlobalTheory.DenseBox

/- English proof (translation)
Establish `e : ((GlobalTheory.StepData.box A c : Submodule 𝒪[k] (A → k)) : Set (A → k)) = ⋂ i : A, (fun y : A → k => y i) ⁻¹' cball c`. Use extensionality with `y`. Simplify using `[GlobalTheory.StepData.mem_box, cball]`. Rewrite using `[e]`. Conclude with `isOpen_iInter_of_finite fun i => (isOpen_cball c).preimage (continuous_apply i)`.
-/
theorem isOpen_box_set {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A : Type) [Fintype A] (c : kˣ) : IsOpen ((GlobalTheory.StepData.box A c : Submodule 𝒪[k] (A → k)) : Set (A → k)) := by
  have e : ((GlobalTheory.StepData.box A c : Submodule 𝒪[k] (A → k)) : Set (A → k)) =
      ⋂ i : A, (fun y : A → k => y i) ⁻¹' cball c := by
    ext y; simp [GlobalTheory.StepData.mem_box, cball]
  rw [e]
  exact isOpen_iInter_of_finite fun i => (isOpen_cball c).preimage (continuous_apply i)

/- English proof (translation)
Introduce `k _ _ _ _ E _ ι hι A B _ _ f hf c hsupp hinv x y`. Establish `hv : DenseRange (fun y : A → E => fun a => ι (y a))` using `DenseRange.piMap (fun _ => hι)`. Establish `hM : DenseRange (fun x : Matrix A B E => x.map ι)`. Establish `: DenseRange (fun x : A → B → E => fun a b => ι (x a b))` using `DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hι))`. Conclude with `this`.

Establish `hF : IsOpen {p : Matrix A B k × (A → k) | f p.1 p.2 = f x y}` using `hf.isOpen_fiber _`. Use `⟨fun hne => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Set `U : Set (Matrix A B k × (A → k))` to `{p | f p.1 p.2 = f x y} ∩ {p | p.2 - y ∈ (GlobalTheory.StepData.box A c⁻¹ : Set (A → k))}`. Establish `hU : IsOpen U` using `hF.inter ((isOpen_box_set A c⁻¹).preimage (continuous_snd.sub continuous_const))`. Establish `hxy : (x, y) ∈ U` using `⟨rfl, by simp⟩`.

Take `⟨⟨x0, y0⟩, hp⟩` from `(hM.prodMap hv).exists_mem_open hU ⟨_, hxy⟩`. Take `⟨h1, h2⟩` from `hp`. Establish `hne' : f (x0.map ι) (fun a => ι (y0 a)) ≠ 0`. Simplify using `only [Set.mem_setOf_eq, Prod.map] at h1`. Rewrite using `[h1]`.

Conclude with `hne`. Establish `hy0` using `hsupp x0 y0 hne'`. Establish `h2' : (fun a => ι (y0 a)) - y ∈ GlobalTheory.StepData.box A c⁻¹` using `h2`. Use `Submodule.sub_mem _ hy0 h2'` as an intermediate fact. Simplify using `using this`.

Establish `hG : IsOpen {p : Matrix A B k × (A → k) | f p.1 p.2 = f x (y + z)}` using `hf.isOpen_fiber _`. Set `V : Set (Matrix A B k × (A → k) × (A → k))` to `{q | f q.1 q.2.1 = f x y} ∩ {q | f q.1 (q.2.1 + q.2.2) = f x (y + z)} ∩ {q | q.2.2 ∈ (GlobalTheory.StepData.box A c : Set (A → k))}`. Establish `hV : IsOpen V`. Use `(IsOpen.inter ?_ ?_).inter ((isOpen_box_set A c).preimage (continuous_snd.comp continuous_snd))` and prove the remaining obligations. Conclude with `hF.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))`.

Conclude with `hG.preimage (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).add (continuous_snd.comp continuous_snd)))`. Establish `hxyz : (x, y, z) ∈ V` using `⟨⟨rfl, rfl⟩, hz⟩`. Take `⟨⟨x0, y0, z0⟩, hp⟩` from `(hM.prodMap (hv.prodMap hv)).exists_mem_open hV ⟨_, hxyz⟩`. Take `⟨⟨h1, h2⟩, h3⟩` from `hp`. Simplify using `only [Set.mem_setOf_eq, Prod.map] at h1 h2 h3`.

Establish `e` using `hinv x0 y0 z0 h3`. Establish `e' : (fun a => ι (y0 a + z0 a)) = (fun a => ι (y0 a)) + (fun a => ι (z0 a))`. Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules. Rewrite `e` using `[e']`.

Rewrite using `[← h2, e, h1]`.
-/
theorem support_invariance_of_dense : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (E : Type) [Field E] (ι : E →+* k), DenseRange ι →
  ∀ (A B : Type) [Fintype A] [Fintype B] (f : Matrix A B k → (A → k) → ℂ), IsLocallyConstant (fun p : Matrix A B k × (A → k) => f p.1 p.2) →
  ∀ (c : kˣ), (∀ (x : Matrix A B E) (y : A → E), f (x.map ι) (fun a => ι (y a)) ≠ 0 → (fun a => ι (y a)) ∈ box A c⁻¹) →
    (∀ (x : Matrix A B E) (y z : A → E), (fun a => ι (z a)) ∈ box A c → f (x.map ι) (fun a => ι (y a + z a)) = f (x.map ι) (fun a => ι (y a))) →
    ∀ x y, (f x y ≠ 0 → y ∈ box A c⁻¹) ∧ ∀ z ∈ box A c, f x (y + z) = f x y := by
  intro k _ _ _ _ E _ ι hι A B _ _ f hf c hsupp hinv x y
  have hv : DenseRange (fun y : A → E => fun a => ι (y a)) := DenseRange.piMap (fun _ => hι)
  have hM : DenseRange (fun x : Matrix A B E => x.map ι) := by
    have : DenseRange (fun x : A → B → E => fun a b => ι (x a b)) :=
      DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hι))
    exact this
  have hF : IsOpen {p : Matrix A B k × (A → k) | f p.1 p.2 = f x y} := hf.isOpen_fiber _
  refine ⟨fun hne => ?_, fun z hz => ?_⟩
  ·
    let U : Set (Matrix A B k × (A → k)) :=
      {p | f p.1 p.2 = f x y} ∩ {p | p.2 - y ∈ (GlobalTheory.StepData.box A c⁻¹ : Set (A → k))}
    have hU : IsOpen U := hF.inter ((isOpen_box_set A c⁻¹).preimage (continuous_snd.sub continuous_const))
    have hxy : (x, y) ∈ U := ⟨rfl, by simp⟩
    obtain ⟨⟨x0, y0⟩, hp⟩ := (hM.prodMap hv).exists_mem_open hU ⟨_, hxy⟩
    obtain ⟨h1, h2⟩ := hp
    have hne' : f (x0.map ι) (fun a => ι (y0 a)) ≠ 0 := by
      simp only [Set.mem_setOf_eq, Prod.map] at h1; rw [h1]; exact hne
    have hy0 := hsupp x0 y0 hne'
    have h2' : (fun a => ι (y0 a)) - y ∈ GlobalTheory.StepData.box A c⁻¹ := h2
    have := Submodule.sub_mem _ hy0 h2'
    simpa using this
  ·
    have hG : IsOpen {p : Matrix A B k × (A → k) | f p.1 p.2 = f x (y + z)} := hf.isOpen_fiber _
    let V : Set (Matrix A B k × (A → k) × (A → k)) :=
      {q | f q.1 q.2.1 = f x y} ∩ {q | f q.1 (q.2.1 + q.2.2) = f x (y + z)} ∩
        {q | q.2.2 ∈ (GlobalTheory.StepData.box A c : Set (A → k))}
    have hV : IsOpen V := by
      refine (IsOpen.inter ?_ ?_).inter ((isOpen_box_set A c).preimage (continuous_snd.comp continuous_snd))
      · exact hF.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
      · exact hG.preimage (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).add
          (continuous_snd.comp continuous_snd)))
    have hxyz : (x, y, z) ∈ V := ⟨⟨rfl, rfl⟩, hz⟩
    obtain ⟨⟨x0, y0, z0⟩, hp⟩ := (hM.prodMap (hv.prodMap hv)).exists_mem_open hV ⟨_, hxyz⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    simp only [Set.mem_setOf_eq, Prod.map] at h1 h2 h3
    have e := hinv x0 y0 z0 h3
    have e' : (fun a => ι (y0 a + z0 a)) = (fun a => ι (y0 a)) + (fun a => ι (z0 a)) := by
      funext a; simp
    rw [e'] at e
    rw [← h2, e, h1]

end GlobalTheory.DenseBox
