import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TwU.SeamEmb

open Formalism.L2.Ker

/- English proof (translation)
Assemble the required witnesses or components as `⟨D.eTau.symm (Classical.arbitrary _)⟩`.
-/
theorem tau_nonempty' (D : D7) : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩

variable {D : D7} {X : Fields} (s : Seam D X)

/- English proof (translation)
Use function extensionality and compare the values at `k`. Distinguish the cases in `h : k = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`.
-/
theorem iE_single {a : ℕ} (j : Fin a) : (fun k => s.iE ((Pi.single j (1 : X.E) : Sp X.E a) k)) = (Pi.single j 1 : Fin a → D.host.E) := by
  funext k
  by_cases h : k = j
  · subst h; simp
  · simp [Pi.single_apply, h]

/- English proof (translation)
Introduce `x x' h`. Use `LinearMap.ext fun v => funext fun l => ?_` and prove the remaining obligations. Establish `e1` using `seamHom_apply s x (fun k => s.iE.symm (v k)) l`. Establish `e2` using `seamHom_apply s x' (fun k => s.iE.symm (v k)) l`. Simplify using `only [RingEquiv.apply_symm_apply] at e1 e2`.

Rewrite using `[← e1, ← e2, h]`.
-/
theorem seamHom_injective {a b : ℕ} : Function.Injective (seamHom s (a := a) (b := b)) := by
  intro x x' h
  refine LinearMap.ext fun v => funext fun l => ?_
  have e1 := seamHom_apply s x (fun k => s.iE.symm (v k)) l
  have e2 := seamHom_apply s x' (fun k => s.iE.symm (v k)) l
  simp only [RingEquiv.apply_symm_apply] at e1 e2
  rw [← e1, ← e2, h]

/- English proof (translation)
Introduce `y`. Use `⟨Matrix.toLin' ((LinearMap.toMatrix' y).map s.iE), ?_⟩` and prove the remaining obligations. Unfold `seamHom`. Rewrite using `[LinearMap.toMatrix'_toLin']`. Establish `: ((LinearMap.toMatrix' y).map s.iE).map s.iE.symm = LinearMap.toMatrix' y`.

Use extensionality with `p q`. Simplify using the standard rewrite rules. Rewrite using `[this, Matrix.toLin'_toMatrix']`.
-/
theorem seamHom_surjective {a b : ℕ} : Function.Surjective (seamHom s (a := a) (b := b)) := by
  intro y
  refine ⟨Matrix.toLin' ((LinearMap.toMatrix' y).map s.iE), ?_⟩
  unfold seamHom
  rw [LinearMap.toMatrix'_toLin']
  have : ((LinearMap.toMatrix' y).map s.iE).map s.iE.symm = LinearMap.toMatrix' y := by
    ext p q; simp
  rw [this, Matrix.toLin'_toMatrix']

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Use `show δ * X.embC s.σ₀ τ (seamHom s x (Pi.single j 1) i) = δ * TaylorLogMetric.embT D (s.iT τ) (x (Pi.single j 1) i)`. Use `congr 1`. Use `show s.σ₀ (X.emb τ _) = _`. Rewrite using `[hs.1, seamHom_apply, iE_single]`.
-/
theorem embH_seamHom (hs : s.Ok) (δ : ℂ) {a b : ℕ} (x : HomE D.host.E a b) :
    embH (X.embC s.σ₀) δ (seamHom s x) = fun τ => embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x (s.iT τ) := by
  funext τ i j
  show δ * X.embC s.σ₀ τ (seamHom s x (Pi.single j 1) i) = δ * TaylorLogMetric.embT D (s.iT τ) (x (Pi.single j 1) i)
  congr 1
  show s.σ₀ (X.emb τ _) = _
  rw [hs.1, seamHom_apply, iE_single]

/- English proof (translation)
Introduce `x y h`. Take `⟨τ⟩` from `(inferInstance : Nonempty ι)`. Use `LinearMap.pi_ext' fun j => LinearMap.ext_ring (funext fun i => ?_)` and prove the remaining obligations. Use `congrFun (congrFun (congrFun h τ) i) j` as an intermediate fact. Simplify using `only [embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this`.

Conclude with `(emb τ).injective (mul_left_cancel₀ hδ this)`.
-/
theorem embH_injective {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] [Nonempty ι]
    (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) {a b : ℕ} : Function.Injective (embH emb δ (a := a) (b := b)) := by
  intro x y h
  obtain ⟨τ⟩ := (inferInstance : Nonempty ι)
  refine LinearMap.pi_ext' fun j => LinearMap.ext_ring (funext fun i => ?_)
  have := congrFun (congrFun (congrFun h τ) i) j
  simp only [embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  exact (emb τ).injective (mul_left_cancel₀ hδ this)

end GlobalTheory.TwU.SeamEmb

namespace GlobalTheory.TwU.SeamEmb

open Formalism.L2.Ker

/- English proof (translation)
Introduce `D X s hs δ a b`. Establish `hemb` using `embH_seamHom s hs δ (a := a) (b := b)`. Establish `hcomp : ∀ (x : HomE D.host.E a b) (v : VV D.what₂.Tau a b), embH (X.embC s.σ₀) δ (seamHom s x) = (fun τ => v (s.iT τ)) ↔ embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x = v`. Introduce `x v`. Rewrite using `[hemb]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `σ`. Use `congrFun h (s.iT.symm σ)` as an intermediate fact. Simplify using `using this`.

Introduce `h`. Rewrite using `[h]`. Use `⟨⟨seamHom_injective s, seamHom_surjective s⟩, hemb, ?_, ?_⟩` and prove the remaining obligations. Introduce `M M' hM v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, hyv⟩`. Take `⟨x, rfl⟩` from `seamHom_surjective s y`. Conclude with `⟨x, (hM x).1 hy, (hcomp x v).1 hyv⟩`. Introduce and unpack `⟨x, hx, hxv⟩`. Conclude with `⟨seamHom s x, (hM x).2 hx, (hcomp x v).2 hxv⟩`.

Introduce `hδ Ξ v haveI : Nonempty D.what₂.Tau := tau_nonempty' D haveI : Nonempty X.Tau := ⟨s.iT.symm (Classical.arbitrary _)⟩`. Establish `hex : (∃ y, embH (X.embC s.σ₀) δ y = fun τ => v (s.iT τ)) ↔ ∃ x, embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x = v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Take `⟨x, rfl⟩` from `seamHom_surjective s y`.

Conclude with `⟨x, (hcomp x v).1 hy⟩`. Introduce and unpack `⟨x, hx⟩`. Conclude with `⟨seamHom s x, (hcomp x v).2 hx⟩`. Unfold `onV`. Distinguish the cases in `h' : ∃ x, embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x = v`.

Establish `h` using `hex.2 h'`. Rewrite using `[dif_pos h, dif_pos h']`. Use `congr 1`. Apply `embH_injective (X.embC s.σ₀) hδ` to reduce the goal to its premises. Rewrite using `[h.choose_spec, (hcomp _ v).2 h'.choose_spec]`.

Establish `h : ¬ ∃ y, embH (X.embC s.σ₀) δ y = fun τ => v (s.iT τ)` using `fun h => h' (hex.1 h)`. Rewrite using `[dif_neg h, dif_neg h']`.
-/
theorem seam_coords : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ (δ : ℂ) {a b : ℕ}, Function.Bijective (seamHom s (a := a) (b := b)) ∧ (∀ x : HomE D.host.E a b, embH (X.embC s.σ₀) δ (seamHom s x) = fun τ => embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x (s.iT τ)) ∧ (∀ (M : Submodule (𝓞 X.E) (HomE X.E a b)) (M' : Submodule (𝓞 D.host.E) (HomE D.host.E a b)), (∀ x, seamHom s x ∈ M ↔ x ∈ M') → ∀ v : VV D.what₂.Tau a b, (fun τ => v (s.iT τ)) ∈ laV (X.embC s.σ₀) δ M ↔ v ∈ laV (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ M') ∧ (δ ≠ 0 → ∀ (Ξ : HomE X.E a b → ℂ) (v : VV D.what₂.Tau a b), onV (X.embC s.σ₀) δ Ξ (fun τ => v (s.iT τ)) = onV (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ (fun x => Ξ (seamHom s x)) v) := by
  intro D X s hs δ a b
  have hemb := embH_seamHom s hs δ (a := a) (b := b)
  have hcomp : ∀ (x : HomE D.host.E a b) (v : VV D.what₂.Tau a b),
      embH (X.embC s.σ₀) δ (seamHom s x) = (fun τ => v (s.iT τ)) ↔ embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x = v := by
    intro x v
    rw [hemb]
    constructor
    · intro h
      funext σ
      have := congrFun h (s.iT.symm σ)
      simpa using this
    · intro h; rw [h]
  refine ⟨⟨seamHom_injective s, seamHom_surjective s⟩, hemb, ?_, ?_⟩
  · intro M M' hM v
    constructor
    · rintro ⟨y, hy, hyv⟩
      obtain ⟨x, rfl⟩ := seamHom_surjective s y
      exact ⟨x, (hM x).1 hy, (hcomp x v).1 hyv⟩
    · rintro ⟨x, hx, hxv⟩
      exact ⟨seamHom s x, (hM x).2 hx, (hcomp x v).2 hxv⟩
  · intro hδ Ξ v
    haveI : Nonempty D.what₂.Tau := tau_nonempty' D
    haveI : Nonempty X.Tau := ⟨s.iT.symm (Classical.arbitrary _)⟩
    have hex : (∃ y, embH (X.embC s.σ₀) δ y = fun τ => v (s.iT τ)) ↔ ∃ x, embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x = v := by
      constructor
      · rintro ⟨y, hy⟩
        obtain ⟨x, rfl⟩ := seamHom_surjective s y
        exact ⟨x, (hcomp x v).1 hy⟩
      · rintro ⟨x, hx⟩
        exact ⟨seamHom s x, (hcomp x v).2 hx⟩
    unfold onV
    by_cases h' : ∃ x, embH (fun τ : D.what₂.Tau => TaylorLogMetric.embT D τ) δ x = v
    · have h := hex.2 h'
      rw [dif_pos h, dif_pos h']
      congr 1
      apply embH_injective (X.embC s.σ₀) hδ
      rw [h.choose_spec, (hcomp _ v).2 h'.choose_spec]
    · have h : ¬ ∃ y, embH (X.embC s.σ₀) δ y = fun τ => v (s.iT τ) := fun h => h' (hex.1 h)
      rw [dif_neg h, dif_neg h']

end GlobalTheory.TwU.SeamEmb
