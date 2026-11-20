import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Isotyp
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

/- English proof (translation)
The claim follows from `(h.eq_bot_or_eq_top (⟨W, fun g _ hv => hW g _ hv⟩ : Subrepresentation ρ)).imp (congrArg Subrepresentation.toSubmodule) (congrArg Subrepresentation.toSubmodule)`.
-/
private theorem irr_sub {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (h : ρ.IsIrreducible) (W : Submodule ℂ V) (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) : W = ⊥ ∨ W = ⊤ :=
  (h.eq_bot_or_eq_top (⟨W, fun g _ hv => hW g _ hv⟩ : Subrepresentation ρ)).imp
    (congrArg Subrepresentation.toSubmodule) (congrArg Subrepresentation.toSubmodule)

/- English proof (translation)
Introduce `F _ _ _ π v σ σ' h X _ _ ρ i hi hρ hs`. Set `T : Set (σ.V →ₗ[ℂ] X)` to `{j | ∀ g u, j (σ.ρ g u) = ρ g (j u)}`. Set `R : Submodule ℂ X` to `⨆ j ∈ T, LinearMap.range j`. Establish `hR : ∀ u, i u ∈ R` using `fun u => by`. Use `Submodule.span_le.2 ?_ (hs u)` and prove the remaining obligations.

Introduce and unpack `_ ⟨p, hp, x, rfl⟩`. Use `(Submodule.span_le (p := R.comap p)).2 ?_ (isotyp F π v σ h x)` and prove the remaining obligations. Introduce and unpack `_ ⟨j, hj, z, rfl⟩`. Conclude with `Submodule.mem_iSup_of_mem (p ∘ₗ j) (Submodule.mem_iSup_of_mem (fun g u => by`. Simplify using `only [LinearMap.comp_apply, hj, hp]) ⟨z, rfl⟩)`.

Establish `irr` using `irr_sub σ.ρ σ.irred`. Establish `irr'` using `irr_sub σ'.ρ σ'.irred`. Choose the witnesses or unpack the hypotheses as in `⟨u₀, hu₀⟩ : ∃ u, i u ≠ 0 := by`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`.

Conclude with `hi (LinearMap.ext hn)`. Choose the witnesses or unpack the hypotheses as in `⟨M, hM⟩ : ∃ M, Maximal (fun N : Submodule ℂ X => (∀ g, ∀ x ∈ N, ρ g x ∈ N) ∧ i u₀ ∉ N) M := by`. Use `(zorn_le_nonempty₀ {N : Submodule ℂ X | (∀ g, ∀ x ∈ N, ρ g x ∈ N) ∧ i u₀ ∉ N} (fun c hc hch y hy => ⟨sSup c, ⟨fun g x hx => ?_, fun hx => ?_⟩, fun z hz => le_sSup hz⟩) ⊥ ⟨fun g x hx => by simp_all, by simpa using hu₀⟩).imp fun M hM => hM.2` and prove the remaining obligations. Take `⟨N, hN, h1⟩` from `(Submodule.mem_sSup_of_directed ⟨y, hy⟩ hch.directedOn).1 hx`. Conclude with `le_sSup hN ((hc hN).1 g x h1)`.

Take `⟨N, hN, h1⟩` from `(Submodule.mem_sSup_of_directed ⟨y, hy⟩ hch.directedOn).1 hx`. Conclude with `(hc hN).2 h1`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj, hjM⟩ : ∃ j ∈ T, ¬ LinearMap.range j ≤ M := by`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`.

Conclude with `hM.1.2 ((iSup₂_le hn : R ≤ M) (hR u₀))`. Establish `hj' : ∀ g u, j (σ.ρ g u) = ρ g (j u)` using `hj`. Establish `k1 : LinearMap.ker (M.mkQ ∘ₗ j) = ⊥` using `(irr _ fun g u hu => by`. Simplify using `only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hu ⊢`. Rewrite using `[hj']; exact hM.1.1 g _ hu).resolve_right fun e => hjM (by`.

Introduce and unpack `_ ⟨z, rfl⟩`. Simplify using `using (e ▸ Submodule.mem_top : z ∈ LinearMap.ker (M.mkQ ∘ₗ j)))`. Establish `k2 : LinearMap.ker (M.mkQ ∘ₗ i) = ⊥` using `(irr' _ fun g u hu => by`. Simplify using `only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hu ⊢`. Rewrite using `[hρ]; exact hM.1.1 g _ hu).resolve_right fun e => hM.1.2 (by`.

Simplify using `using (e ▸ Submodule.mem_top : u₀ ∈ LinearMap.ker (M.mkQ ∘ₗ i)))`. Establish `big : i u₀ ∈ M ⊔ LinearMap.range j`. Assume the negation of the conclusion as `hn`. Use `hjM (le_sup_right.trans (hM.2 ⟨fun g x hx => ?_, hn⟩ le_sup_left))` and prove the remaining obligations. Take `⟨m, hm, _, ⟨z, rfl⟩, rfl⟩` from `Submodule.mem_sup.1 hx`.

Rewrite using `[map_add, ← hj']`. Conclude with `Submodule.add_mem_sup (hM.1.1 g m hm) ⟨_, rfl⟩`. Establish `hu0 : u₀ ≠ 0` using `fun e => hu₀ (by rw [e, map_zero])`. Establish `s1 : (M ⊔ LinearMap.range j).comap i = ⊤` using `(irr' _ fun g u hu => by`. Take `⟨m, hm, _, ⟨z, rfl⟩, e⟩` from `Submodule.mem_sup.1 hu`.

Rewrite using `[Submodule.mem_comap, hρ, ← e, map_add, ← hj']`. Conclude with `Submodule.add_mem_sup (hM.1.1 g m hm) ⟨_, rfl⟩).resolve_left fun e => hu0 (by`. Establish `: u₀ ∈ (M ⊔ LinearMap.range j).comap i` using `big`. Rewrite using `[e, Submodule.mem_bot] at this)` and apply the resulting hypothesis. Establish `s2 : (M ⊔ LinearMap.range i).comap j = ⊤` using `(irr _ fun g u hu => by`.

Take `⟨m, hm, _, ⟨z, rfl⟩, e⟩` from `Submodule.mem_sup.1 hu`. Rewrite using `[Submodule.mem_comap, hj', ← e, map_add, ← hρ]`. Conclude with `Submodule.add_mem_sup (hM.1.1 g m hm) ⟨_, rfl⟩).resolve_left fun e => by`. Take `⟨m, hm, _, ⟨z, rfl⟩, e'⟩` from `Submodule.mem_sup.1 big`. Establish `hz : z ∈ (M ⊔ LinearMap.range i).comap j`.

Rewrite using `[Submodule.mem_comap, eq_sub_of_add_eq' e', sub_eq_neg_add]`. Conclude with `Submodule.add_mem_sup (neg_mem hm) ⟨_, rfl⟩`. Rewrite `hz` using `[e, Submodule.mem_bot]`. Rewrite `e'` using `[hz, map_zero, add_zero]`. Conclude with `hM.1.2 (e' ▸ hm)`.

Establish `q : ∀ {Y Z : Type} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z] (a : Y →ₗ[ℂ] X) (b : Z →ₗ[ℂ] X), (M ⊔ LinearMap.range b).comap a = ⊤ → LinearMap.range (M.mkQ ∘ₗ a) ≤ LinearMap.range (M.mkQ ∘ₗ b)`. Introduce `Y Z _ _ _ _ a b e`. Introduce and unpack `_ ⟨y, rfl⟩`. Take `⟨m, hm, _, ⟨z, rfl⟩, e'⟩` from `Submodule.mem_sup.1 (show y ∈ (M ⊔ LinearMap.range b).comap a from e ▸ Submodule.mem_top)`. Conclude with `⟨z, by simp [← e', (Submodule.Quotient.mk_eq_zero M).2 hm]⟩`.

Establish `er` using `le_antisymm (q j i s2) (q i j s1)`. Set `e` to `(LinearEquiv.ofInjective _ (LinearMap.ker_eq_bot.1 k1)).trans ((LinearEquiv.ofEq _ _ er).trans (LinearEquiv.ofInjective _ (LinearMap.ker_eq_bot.1 k2)).symm)`. Establish `he : ∀ u, (M.mkQ ∘ₗ i) (e u) = (M.mkQ ∘ₗ j) u` using `fun u => congrArg Subtype.val ((LinearEquiv.ofInjective _ (LinearMap.ker_eq_bot.1 k2)).apply_symm_apply _)`. Use `⟨e, fun g u => LinearMap.ker_eq_bot.1 k2 ?_⟩` and prove the remaining obligations. Establish `h1` using `he u`.

Rewrite using `[he]`. Simplify using `only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h1 ⊢`. Rewrite using `[hj', hρ, ← map_sub]`. Conclude with `hM.1.1 g _ (by simpa using neg_mem h1)`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Pp.isotypQuot :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.IsotypQuot F := by
  intro F _ _ _ π v σ σ' h X _ _ ρ i hi hρ hs
  let T : Set (σ.V →ₗ[ℂ] X) := {j | ∀ g u, j (σ.ρ g u) = ρ g (j u)}
  let R : Submodule ℂ X := ⨆ j ∈ T, LinearMap.range j
  have hR : ∀ u, i u ∈ R := fun u => by
    refine Submodule.span_le.2 ?_ (hs u)
    rintro _ ⟨p, hp, x, rfl⟩
    refine (Submodule.span_le (p := R.comap p)).2 ?_ (isotyp F π v σ h x)
    rintro _ ⟨j, hj, z, rfl⟩
    exact Submodule.mem_iSup_of_mem (p ∘ₗ j) (Submodule.mem_iSup_of_mem (fun g u => by
      simp only [LinearMap.comp_apply, hj, hp]) ⟨z, rfl⟩)
  have irr := irr_sub σ.ρ σ.irred
  have irr' := irr_sub σ'.ρ σ'.irred
  obtain ⟨u₀, hu₀⟩ : ∃ u, i u ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hi (LinearMap.ext hn)
  obtain ⟨M, hM⟩ : ∃ M, Maximal (fun N : Submodule ℂ X => (∀ g, ∀ x ∈ N, ρ g x ∈ N) ∧ i u₀ ∉ N) M := by
    refine (zorn_le_nonempty₀ {N : Submodule ℂ X | (∀ g, ∀ x ∈ N, ρ g x ∈ N) ∧ i u₀ ∉ N}
      (fun c hc hch y hy => ⟨sSup c, ⟨fun g x hx => ?_, fun hx => ?_⟩,
      fun z hz => le_sSup hz⟩) ⊥ ⟨fun g x hx => by simp_all, by simpa using hu₀⟩).imp fun M hM => hM.2
    · obtain ⟨N, hN, h1⟩ := (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hch.directedOn).1 hx
      exact le_sSup hN ((hc hN).1 g x h1)
    · obtain ⟨N, hN, h1⟩ := (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hch.directedOn).1 hx
      exact (hc hN).2 h1
  obtain ⟨j, hj, hjM⟩ : ∃ j ∈ T, ¬ LinearMap.range j ≤ M := by
    by_contra hn
    push Not at hn
    exact hM.1.2 ((iSup₂_le hn : R ≤ M) (hR u₀))
  have hj' : ∀ g u, j (σ.ρ g u) = ρ g (j u) := hj
  have k1 : LinearMap.ker (M.mkQ ∘ₗ j) = ⊥ := (irr _ fun g u hu => by
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hu ⊢
      rw [hj']; exact hM.1.1 g _ hu).resolve_right fun e => hjM (by
      rintro _ ⟨z, rfl⟩
      simpa using (e ▸ Submodule.mem_top : z ∈ LinearMap.ker (M.mkQ ∘ₗ j)))
  have k2 : LinearMap.ker (M.mkQ ∘ₗ i) = ⊥ := (irr' _ fun g u hu => by
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hu ⊢
      rw [hρ]; exact hM.1.1 g _ hu).resolve_right fun e => hM.1.2 (by
      simpa using (e ▸ Submodule.mem_top : u₀ ∈ LinearMap.ker (M.mkQ ∘ₗ i)))
  have big : i u₀ ∈ M ⊔ LinearMap.range j := by
    by_contra hn
    refine hjM (le_sup_right.trans (hM.2 ⟨fun g x hx => ?_, hn⟩ le_sup_left))
    obtain ⟨m, hm, _, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, ← hj']
    exact Submodule.add_mem_sup (hM.1.1 g m hm) ⟨_, rfl⟩
  have hu0 : u₀ ≠ 0 := fun e => hu₀ (by rw [e, map_zero])
  have s1 : (M ⊔ LinearMap.range j).comap i = ⊤ := (irr' _ fun g u hu => by
      obtain ⟨m, hm, _, ⟨z, rfl⟩, e⟩ := Submodule.mem_sup.1 hu
      rw [Submodule.mem_comap, hρ, ← e, map_add, ← hj']
      exact Submodule.add_mem_sup (hM.1.1 g m hm) ⟨_, rfl⟩).resolve_left fun e => hu0 (by
      have : u₀ ∈ (M ⊔ LinearMap.range j).comap i := big
      rwa [e, Submodule.mem_bot] at this)
  have s2 : (M ⊔ LinearMap.range i).comap j = ⊤ := (irr _ fun g u hu => by
      obtain ⟨m, hm, _, ⟨z, rfl⟩, e⟩ := Submodule.mem_sup.1 hu
      rw [Submodule.mem_comap, hj', ← e, map_add, ← hρ]
      exact Submodule.add_mem_sup (hM.1.1 g m hm) ⟨_, rfl⟩).resolve_left fun e => by
      obtain ⟨m, hm, _, ⟨z, rfl⟩, e'⟩ := Submodule.mem_sup.1 big
      have hz : z ∈ (M ⊔ LinearMap.range i).comap j := by
        rw [Submodule.mem_comap, eq_sub_of_add_eq' e', sub_eq_neg_add]
        exact Submodule.add_mem_sup (neg_mem hm) ⟨_, rfl⟩
      rw [e, Submodule.mem_bot] at hz
      rw [hz, map_zero, add_zero] at e'
      exact hM.1.2 (e' ▸ hm)
  have q : ∀ {Y Z : Type} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z] (a : Y →ₗ[ℂ] X) (b : Z →ₗ[ℂ] X),
      (M ⊔ LinearMap.range b).comap a = ⊤ → LinearMap.range (M.mkQ ∘ₗ a) ≤ LinearMap.range (M.mkQ ∘ₗ b) := by
    intro Y Z _ _ _ _ a b e
    rintro _ ⟨y, rfl⟩
    obtain ⟨m, hm, _, ⟨z, rfl⟩, e'⟩ := Submodule.mem_sup.1 (show y ∈ (M ⊔ LinearMap.range b).comap a from e ▸ Submodule.mem_top)
    exact ⟨z, by simp [← e', (Submodule.Quotient.mk_eq_zero M).2 hm]⟩
  have er := le_antisymm (q j i s2) (q i j s1)
  let e := (LinearEquiv.ofInjective _ (LinearMap.ker_eq_bot.1 k1)).trans
    ((LinearEquiv.ofEq _ _ er).trans (LinearEquiv.ofInjective _ (LinearMap.ker_eq_bot.1 k2)).symm)
  have he : ∀ u, (M.mkQ ∘ₗ i) (e u) = (M.mkQ ∘ₗ j) u := fun u =>
    congrArg Subtype.val ((LinearEquiv.ofInjective _ (LinearMap.ker_eq_bot.1 k2)).apply_symm_apply _)
  refine ⟨e, fun g u => LinearMap.ker_eq_bot.1 k2 ?_⟩
  have h1 := he u
  rw [he]
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h1 ⊢
  rw [hj', hρ, ← map_sub]
  exact hM.1.1 g _ (by simpa using neg_mem h1)
