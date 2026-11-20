import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ContraSq

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Introduce `s` and use `by have e : {g : G | S.toRepresentation g s = s} = {g : G | ρ g (s : V) = s} := by ext g exact Subtype.ext_iff rw [e] exact hρ s`.
-/
theorem isSmooth_sub {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (S : Subrepresentation ρ) :
    IsSmooth S.toRepresentation := fun s => by
  have e : {g : G | S.toRepresentation g s = s} = {g : G | ρ g (s : V) = s} := by
    ext g
    exact Subtype.ext_iff
  rw [e]
  exact hρ s

/- English proof (translation)
Establish `hmem : ∀ x : fixed S.toRepresentation K, (S.toSubmodule.subtype ∘ₗ (fixed S.toRepresentation K).subtype) x ∈ fixed ρ K`. Introduce `x`. Use `GlobalTheory.ContraRefl.mem_fix.2 fun h hh => ?_` and prove the remaining obligations. Conclude with `congrArg Subtype.val (GlobalTheory.ContraRefl.mem_fix.1 x.2 h hh)`. Set `ι : fixed S.toRepresentation K →ₗ[ℂ] fixed ρ K` to `LinearMap.codRestrict _ _ hmem`.

Establish `hι : LinearMap.ker ι = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `x hx`. Establish `h1 : ((x : S.toSubmodule) : V) = 0` using `congrArg Subtype.val hx`. Conclude with `Subtype.ext (Subtype.ext h1)`.

Take `⟨r, hr⟩` from `LinearMap.exists_leftInverse_of_injective ι hι`. Take `⟨l, hl1, hl2⟩` from `GlobalTheory.ContraRefl.exists_fixed_contra hρ ho hc ((l₀ ∘ₗ (fixed S.toRepresentation K).subtype) ∘ₗ r)`. Use `⟨l, hl1, fun s => ?_⟩` and prove the remaining obligations. Establish `key : (l : Module.Dual ℂ V) ∘ₗ S.toSubmodule.subtype = l₀`. Use `GlobalTheory.ContraRefl.form_ext (isSmooth_sub hρ S) hc (fun h hh w => ?_) hl₀ fun w hw => ?_` and prove the remaining obligations.

Establish `h1` using `congrArg (fun x : smoothPart ρ.dual => (x : Module.Dual ℂ V) (w : V)) (hl1 h⁻¹ (inv_mem hh))`. Simplify using `only [contra_apply, inv_inv] at h1`. Conclude with `h1`. Establish `h2` using `hl2 (ι ⟨w, hw⟩)`. Establish `h3 : r (ι ⟨w, hw⟩) = ⟨w, hw⟩` using `LinearMap.congr_fun hr ⟨w, hw⟩`.

Simplify using `only [LinearMap.comp_apply, h3] at h2`. Conclude with `h2`. Conclude with `LinearMap.congr_fun key s`.
-/
theorem exists_smooth_extension {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (S : Subrepresentation ρ)
    {K : Subgroup G} (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G))
    (l₀ : Module.Dual ℂ S.toSubmodule) (hl₀ : ∀ h ∈ K, ∀ s, l₀ (S.toRepresentation h s) = l₀ s) :
    ∃ l : smoothPart ρ.dual, (∀ h ∈ K, contra ρ h l = l) ∧
      ∀ s : S.toSubmodule, (l : Module.Dual ℂ V) s = l₀ s := by
  have hmem : ∀ x : fixed S.toRepresentation K,
      (S.toSubmodule.subtype ∘ₗ (fixed S.toRepresentation K).subtype) x ∈ fixed ρ K := by
    intro x
    refine GlobalTheory.ContraRefl.mem_fix.2 fun h hh => ?_
    exact congrArg Subtype.val (GlobalTheory.ContraRefl.mem_fix.1 x.2 h hh)
  let ι : fixed S.toRepresentation K →ₗ[ℂ] fixed ρ K := LinearMap.codRestrict _ _ hmem
  have hι : LinearMap.ker ι = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h1 : ((x : S.toSubmodule) : V) = 0 := congrArg Subtype.val hx
    exact Subtype.ext (Subtype.ext h1)
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ι hι
  obtain ⟨l, hl1, hl2⟩ := GlobalTheory.ContraRefl.exists_fixed_contra hρ ho hc
    ((l₀ ∘ₗ (fixed S.toRepresentation K).subtype) ∘ₗ r)
  refine ⟨l, hl1, fun s => ?_⟩
  have key : (l : Module.Dual ℂ V) ∘ₗ S.toSubmodule.subtype = l₀ := by
    refine GlobalTheory.ContraRefl.form_ext (isSmooth_sub hρ S) hc (fun h hh w => ?_) hl₀ fun w hw => ?_
    · have h1 := congrArg (fun x : smoothPart ρ.dual => (x : Module.Dual ℂ V) (w : V))
        (hl1 h⁻¹ (inv_mem hh))
      simp only [contra_apply, inv_inv] at h1
      exact h1
    · have h2 := hl2 (ι ⟨w, hw⟩)
      have h3 : r (ι ⟨w, hw⟩) = ⟨w, hw⟩ := LinearMap.congr_fun hr ⟨w, hw⟩
      simp only [LinearMap.comp_apply, h3] at h2
      exact h2
  exact LinearMap.congr_fun key s

def annih {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (S : Subrepresentation ρ)
    (f : S.toRepresentation.IntertwiningMap τ) : Subrepresentation (contra ρ) :=
  ⟨{ carrier := {l | ∀ s : S.toSubmodule, f s = 0 → (l : Module.Dual ℂ V) s = 0}
     add_mem' := fun {a b} ha hb s hs => by simp [ha s hs, hb s hs]
     zero_mem' := fun s _ => by simp
     smul_mem' := fun c a ha s hs => by simp [ha s hs] }, by
    intro h l hl s hs
    have h0 : f (S.toRepresentation h⁻¹ s) = 0 := by
      rw [f.isIntertwining, hs, map_zero]
    exact hl _ h0⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_annih {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} {l : smoothPart ρ.dual} :
    l ∈ (annih S f).toSubmodule ↔ ∀ s : S.toSubmodule, f s = 0 → (l : Module.Dual ℂ V) s = 0 :=
  Iff.rfl

def pull {ρ : Representation ℂ G V} (S : Subrepresentation ρ) (g : W →ₗ[ℂ] S.toSubmodule) :
    Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ W :=
  (S.toSubmodule.subtype ∘ₗ g).dualMap

/- English proof (translation)
Establish `h0 : f (g (f s) - s) = 0`. Establish `: f (g (f s) - s) = f (g (f s)) - f s` using `map_sub f.toLinearMap _ _`. Rewrite using `[this, hg, sub_self]`. Establish `h1` using `mem_annih.1 hl _ h0`. Establish `h2 : (l : Module.Dual ℂ V) ((g (f s) : V) - s) = 0` using `h1`.

Rewrite `h2` using `[map_sub, sub_eq_zero]`. Conclude with `h2`.
-/
theorem pull_apply_map {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} {g : W →ₗ[ℂ] S.toSubmodule}
    (hg : ∀ w, f (g w) = w) {l : smoothPart ρ.dual} (hl : l ∈ (annih S f).toSubmodule)
    (s : S.toSubmodule) : pull S g (l : Module.Dual ℂ V) (f s) = (l : Module.Dual ℂ V) s := by
  have h0 : f (g (f s) - s) = 0 := by
    have : f (g (f s) - s) = f (g (f s)) - f s := map_sub f.toLinearMap _ _
    rw [this, hg, sub_self]
  have h1 := mem_annih.1 hl _ h0
  have h2 : (l : Module.Dual ℂ V) ((g (f s) : V) - s) = 0 := h1
  rw [map_sub, sub_eq_zero] at h2
  exact h2

def restrLin {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} (hf : Function.Surjective f)
    {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w) :
    (annih S f).toSubmodule →ₗ[ℂ] smoothPart τ.dual where
  toFun l := ⟨pull S g ((l : smoothPart ρ.dual) : Module.Dual ℂ V),
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      ((isSmooth_contra ρ (l : smoothPart ρ.dual)).mem_nhds (by simp)) fun h hh => by
        have hh' : contra ρ h (l : smoothPart ρ.dual) = l := hh
        refine LinearMap.ext fun w => ?_
        obtain ⟨s, rfl⟩ := hf w
        show pull S g _ (τ h⁻¹ (f s)) = pull S g _ (f s)
        rw [← f.isIntertwining, pull_apply_map hg l.2, pull_apply_map hg l.2]
        have h1 := congrArg (fun x : smoothPart ρ.dual => (x : Module.Dual ℂ V) (s : V)) hh'
        simp only [contra_apply] at h1
        exact h1)⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' c a := Subtype.ext (by simp)

/- English proof (translation)
The claim follows from `pull_apply_map hg l.2 s`.
-/
theorem restrLin_apply_map {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    {S : Subrepresentation ρ} {f : S.toRepresentation.IntertwiningMap τ}
    (hf : Function.Surjective f) {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w)
    (l : (annih S f).toSubmodule) (s : S.toSubmodule) :
    (restrLin hf hg l : Module.Dual ℂ W) (f s) = ((l : smoothPart ρ.dual) : Module.Dual ℂ V) s :=
  pull_apply_map hg l.2 s

/- English proof (translation)
Establish `e : ∀ s : S.toSubmodule, (restrLin hf hg ((annih S f).toRepresentation h l) : Module.Dual ℂ W) (f s) = (restrLin hf hg l : Module.Dual ℂ W) (τ h⁻¹ (f s))` using `fun s => by`. Rewrite using `[← f.isIntertwining, restrLin_apply_map, restrLin_apply_map]`. Both sides reduce to the same expression. Use `e (g w)` as an intermediate fact. Rewrite `this` using `[hg w]`. Then use the resulting hypothesis.
-/
theorem restrLin_comm {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    {S : Subrepresentation ρ} {f : S.toRepresentation.IntertwiningMap τ}
    (hf : Function.Surjective f) {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w)
    (h : G) (l : (annih S f).toSubmodule) (w : W) :
    (restrLin hf hg ((annih S f).toRepresentation h l) : Module.Dual ℂ W) w =
      (restrLin hf hg l : Module.Dual ℂ W) (τ h⁻¹ w) := by
  have e : ∀ s : S.toSubmodule,
      (restrLin hf hg ((annih S f).toRepresentation h l) : Module.Dual ℂ W) (f s) =
        (restrLin hf hg l : Module.Dual ℂ W) (τ h⁻¹ (f s)) := fun s => by
    rw [← f.isIntertwining, restrLin_apply_map, restrLin_apply_map]
    rfl
  have := e (g w)
  rwa [hg w] at this

def restr {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} (hf : Function.Surjective f)
    {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w) :
    (annih S f).toRepresentation.IntertwiningMap (contra τ) where
  toLinearMap := restrLin hf hg
  isIntertwining' h :=
    LinearMap.ext fun l => Subtype.ext (LinearMap.ext fun w => restrLin_comm hf hg h l w)

/- English proof (translation)
Introduce `G V W _ _ _ _ _ _ _ hG ρ τ hρ ⟨S, f, hf⟩`. Take `⟨g, hg⟩` from `LinearMap.exists_rightInverse_of_surjective f.toLinearMap (LinearMap.range_eq_top.2 hf)`. Establish `hg' : ∀ w, f (g w) = w` using `fun w => LinearMap.congr_fun hg w`. Use `⟨annih S f, restr hf hg', fun m => ?_⟩` and prove the remaining obligations. Take `⟨K, ho, hc, hKs⟩` from `hG _ ((isSmooth_contra τ m).mem_nhds (by simp))`.

Establish `hfix : ∀ h ∈ K, ∀ s, (m : Module.Dual ℂ W) (f (S.toRepresentation h s)) = (m : Module.Dual ℂ W) (f s)`. Introduce `h hh s`. Establish `h1 : contra τ h⁻¹ m = m` using `hKs (inv_mem hh)`. Establish `h2` using `congrArg (fun x : smoothPart τ.dual => (x : Module.Dual ℂ W) (f s)) h1`. Simplify using `only [contra_apply, inv_inv] at h2`.

Rewrite using `[f.isIntertwining]`. Conclude with `h2`. Take `⟨l, -, hl⟩` from `exists_smooth_extension hρ S ho hc ((m : Module.Dual ℂ W) ∘ₗ f.toLinearMap) hfix`. Establish `hmem : l ∈ (annih S f).toSubmodule` using `fun s hs => by`. Establish `h1` using `hl s`.

Establish `h2 : ((m : Module.Dual ℂ W) ∘ₗ f.toLinearMap) s = (m : Module.Dual ℂ W) (f s)` using `rfl`. Rewrite using `[h1, h2, hs, map_zero]`. Use `⟨⟨l, hmem⟩, Subtype.ext (LinearMap.ext fun w => ?_)⟩` and prove the remaining obligations. Take `⟨s, rfl⟩` from `hf w`. Use `show pull S g (l : Module.Dual ℂ V) (f s) = _`.

Rewrite using `[pull_apply_map hg' hmem]`. Conclude with `hl s`.
-/
theorem contra_isSubquotient : ∀ {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W],
    (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) →
    ∀ (ρ : Representation ℂ G V) (τ : Representation ℂ G W),
      IsSmooth ρ → IsSubquotient τ ρ → IsSubquotient (contra τ) (contra ρ) := by
  intro G V W _ _ _ _ _ _ _ hG ρ τ hρ ⟨S, f, hf⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective f.toLinearMap
    (LinearMap.range_eq_top.2 hf)
  have hg' : ∀ w, f (g w) = w := fun w => LinearMap.congr_fun hg w
  refine ⟨annih S f, restr hf hg', fun m => ?_⟩
  obtain ⟨K, ho, hc, hKs⟩ := hG _ ((isSmooth_contra τ m).mem_nhds (by simp))
  have hfix : ∀ h ∈ K, ∀ s, (m : Module.Dual ℂ W) (f (S.toRepresentation h s)) =
      (m : Module.Dual ℂ W) (f s) := by
    intro h hh s
    have h1 : contra τ h⁻¹ m = m := hKs (inv_mem hh)
    have h2 := congrArg (fun x : smoothPart τ.dual => (x : Module.Dual ℂ W) (f s)) h1
    simp only [contra_apply, inv_inv] at h2
    rw [f.isIntertwining]
    exact h2
  obtain ⟨l, -, hl⟩ := exists_smooth_extension hρ S ho hc
    ((m : Module.Dual ℂ W) ∘ₗ f.toLinearMap) hfix
  have hmem : l ∈ (annih S f).toSubmodule := fun s hs => by
    have h1 := hl s
    have h2 : ((m : Module.Dual ℂ W) ∘ₗ f.toLinearMap) s = (m : Module.Dual ℂ W) (f s) := rfl
    rw [h1, h2, hs, map_zero]
  refine ⟨⟨l, hmem⟩, Subtype.ext (LinearMap.ext fun w => ?_)⟩
  obtain ⟨s, rfl⟩ := hf w
  show pull S g (l : Module.Dual ℂ V) (f s) = _
  rw [pull_apply_map hg' hmem]
  exact hl s

end GlobalTheory.CompanionTheory.ContraSq

end
