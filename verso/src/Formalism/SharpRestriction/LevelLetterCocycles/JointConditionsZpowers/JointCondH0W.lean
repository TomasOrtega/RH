import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.InvariantsConstantConditions
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTame
import Formalism.SharpRestriction.LevelLetterCocycles.ColumnH0Lengths

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

open NumberField IsDedekindDomain

section Phi

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨u, rfl⟩`. Establish `: (LinearMap.compLeft (Algebra.linearMap O K) (Fin k)) u = ∑ j, u j • (Pi.single j 1 : Fin k → K)`. Use function extensionality and compare the values at `a`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single a]`.

Simplify using `[Algebra.smul_def]`. Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne (Ne.symm hb)]`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Use `⟨Pi.single j 1, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a`.

Distinguish the cases in `h : a = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`.
-/
theorem stdG_span (O K : Type) [CommRing O] [Field K] [Algebra O K] (k : ℕ) :
    stdG O K k = Submodule.span O (Set.range fun j : Fin k => (Pi.single j 1 : Fin k → K)) := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    have : (LinearMap.compLeft (Algebra.linearMap O K) (Fin k)) u = ∑ j, u j • (Pi.single j 1 : Fin k → K) := by
      funext a
      rw [Finset.sum_apply, Finset.sum_eq_single a]
      · simp [Algebra.smul_def]
      · intro b _ hb
        simp [Pi.single_eq_of_ne (Ne.symm hb)]
      · simp
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    funext a
    by_cases h : a = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot (τ₁₂ := (D.nbr i w hw).eO.toRingHom), eq_bot_iff]`. Introduce `x hx`. Take `⟨u, rfl⟩` from `Submodule.mkQ_surjective _ x`. Rewrite `hx` using `[LinearMap.mem_ker]`. Rewrite using `[Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Establish `h1 : Br.vecS (D.nbr i w hw) k u ∈ stdG (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) k`. Rewrite using `[← Submodule.Quotient.mk_eq_zero]`. Conclude with `hx`. Take `⟨c, hc⟩` from `h1`. Use `⟨fun j => (D.nbr i w hw).eO.symm (c j), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `j`. Apply `(Br.toLLK (D.nbr i w hw)).injective` to reduce the goal to its premises. Use `congrFun hc j` as an intermediate fact. Simplify using `only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply] at this`. Use `show Br.toLLK (D.nbr i w hw) (algebraMap _ _ ((D.nbr i w hw).eO.symm (c j))) = Br.toLLK (D.nbr i w hw) (u j)`.

Rewrite using `[Br.toLLK_alg, RingEquiv.apply_symm_apply]`. Conclude with `this`.
-/
theorem phi_injective (k : ℕ) : Function.Injective (Br.phi (D.nbr i w hw) k) := by
  rw [← LinearMap.ker_eq_bot (τ₁₂ := (D.nbr i w hw).eO.toRingHom), eq_bot_iff]
  intro x hx
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have h1 : Br.vecS (D.nbr i w hw) k u ∈ stdG (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) k := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact hx
  obtain ⟨c, hc⟩ := h1
  refine ⟨fun j => (D.nbr i w hw).eO.symm (c j), ?_⟩
  funext j
  apply (Br.toLLK (D.nbr i w hw)).injective
  have := congrFun hc j
  simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply] at this
  show Br.toLLK (D.nbr i w hw) (algebraMap _ _ ((D.nbr i w hw).eO.symm (c j))) = Br.toLLK (D.nbr i w hw) (u j)
  rw [Br.toLLK_alg, RingEquiv.apply_symm_apply]
  exact this

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Take `⟨u, rfl⟩` from `Submodule.mkQ_surjective _ x`. Establish `key : Br.vecS (D.nbr i w hw) k ((matRep (mapM (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) M) (Br.ι (D.nbr i w hw) g)) u) = (matRep (Br.locM (D.nbr i w hw) M) g) (Br.vecS (D.nbr i w hw) k u)`. Use function extensionality and compare the values at `p`. Use `show Br.toLLK (D.nbr i w hw) (((mapM (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) M (Br.ι (D.nbr i w hw) g)).mulVec u) p) = ((Br.locM (D.nbr i w hw) M g).mulVec (fun j => Br.toLLK (D.nbr i w hw) (u j))) p`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul]`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Use `congr 1`. Use `show Br.toLLK (D.nbr i w hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (M (Br.ι (D.nbr i w hw) g) p q)) = _`. Rewrite using `[Br.toLLK_alg]`. Both sides reduce to the same expression.

Conclude with `congrArg (fun z : Fin k → Br.LLw (D.nbr i w hw) => (Submodule.Quotient.mk z : (Fin k → Br.LLw (D.nbr i w hw)) ⧸ stdG (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) k)) key`.
-/
theorem phi_act {k : ℕ} (M : Gw D.nd w →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : ↥(GK (D.nbr i w hw).Kw))
    (x : KOG (D.nd.O i) k) :
    Br.phi (D.nbr i w hw) k (actD (stdLatG (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))) M)
      (Br.ι (D.nbr i w hw) g) x) = actD (Br.lat (D.nbr i w hw) M) g (Br.phi (D.nbr i w hw) k x) := by
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective _ x
  have key : Br.vecS (D.nbr i w hw) k ((matRep (mapM (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) M)
      (Br.ι (D.nbr i w hw) g)) u) = (matRep (Br.locM (D.nbr i w hw) M) g) (Br.vecS (D.nbr i w hw) k u) := by
    funext p
    show Br.toLLK (D.nbr i w hw) (((mapM (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) M
        (Br.ι (D.nbr i w hw) g)).mulVec u) p) =
      ((Br.locM (D.nbr i w hw) M g).mulVec (fun j => Br.toLLK (D.nbr i w hw) (u j))) p
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    show Br.toLLK (D.nbr i w hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (M (Br.ι (D.nbr i w hw) g) p q)) = _
    rw [Br.toLLK_alg]
    rfl
  exact congrArg (fun z : Fin k → Br.LLw (D.nbr i w hw) =>
    (Submodule.Quotient.mk z : (Fin k → Br.LLw (D.nbr i w hw)) ⧸ stdG (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) k)) key

end Phi

/- English proof (translation)
Unfold `lenUnit`. Use `set A := Module.length O M`. Use `set B := Module.length O (O ⧸ Ideal.span {(l : O)})`. Establish `hnc : (0 : ℝ) ≤ (n : ℝ) * (c : ℝ)` using `by positivity`. Distinguish the cases in `hB : B.toNat = 0`.

Rewrite using `[hB, Nat.cast_zero, div_zero]`. Simplify using `using hnc`. Establish `hBt : B ≠ ⊤` using `fun h => hB (by rw [h]; rfl)`. Take `⟨m, hm⟩` from `ENat.ne_top_iff_exists.1 hBt`. Rewrite `h`, `hB`, the goal using `[← hm]`.

Establish `h' : A ≤ ((n * c * m : ℕ) : ℕ∞)` using `by simpa using h`. Establish `h1 : A.toNat ≤ n * c * m`. Use `ENat.toNat_le_toNat h' (ENat.coe_ne_top _)` as an intermediate fact. Simplify using `using this`. Simplify using `only [ENat.toNat_coe] at hB ⊢`.

Establish `hBpos : (0 : ℚ) < (m : ℚ)` using `by exact_mod_cast Nat.pos_of_ne_zero hB`. Establish `h2 : ((A.toNat : ℚ) / (m : ℚ)) ≤ (n : ℚ) * (c : ℚ)`. Rewrite using `[div_le_iff₀ hBpos]`. Conclude with `h1` after adjusting the coercions. Conclude with `h2` after adjusting the coercions.
-/
theorem lenUnit_le {O : Type} [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M] (n c : ℕ)
    (h : Module.length O M ≤ (n : ℕ∞) * (c : ℕ∞) * Module.length O (O ⧸ Ideal.span {(l : O)})) :
    (lenUnit (O := O) l M : ℝ) ≤ (n : ℝ) * (c : ℝ) := by
  unfold lenUnit
  set A := Module.length O M
  set B := Module.length O (O ⧸ Ideal.span {(l : O)})
  have hnc : (0 : ℝ) ≤ (n : ℝ) * (c : ℝ) := by positivity
  by_cases hB : B.toNat = 0
  · rw [hB, Nat.cast_zero, div_zero]
    simpa using hnc
  · have hBt : B ≠ ⊤ := fun h => hB (by rw [h]; rfl)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hBt
    rw [← hm] at h hB ⊢
    have h' : A ≤ ((n * c * m : ℕ) : ℕ∞) := by simpa using h
    have h1 : A.toNat ≤ n * c * m := by
      have := ENat.toNat_le_toNat h' (ENat.coe_ne_top _)
      simpa using this
    simp only [ENat.toNat_coe] at hB ⊢
    have hBpos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hB
    have h2 : ((A.toNat : ℚ) / (m : ℚ)) ≤ (n : ℚ) * (c : ℚ) := by
      rw [div_le_iff₀ hBpos]
      exact_mod_cast h1
    exact_mod_cast h2

def wLat (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hu : u ∈ placesOver D.host.E (D.nd.l i))
    (hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u))) g v) :
    LocLat ↥(GK (D.nbr i u hu).Kw) ℚ_[D.nd.l i] (Br.LLw (D.nbr i u hu)) (Br.Ow (D.nbr i u hu)) :=
  { V := Fin D.R.r → Br.LLw (D.nbr i u hu)
    ρ := matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u)))
    cont := hc
    L := Br.lat (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u)) }

def JointCond_H0W (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (X : Formalism.MainNotions.N.KillingConditions.HubData D) (M0 h0 : ℕ) : Prop :=
  ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D → Formalism.MainNotions.TwistedPlaces.SplitK D (D.nd.l i) →
    ∀ u ∈ (X.dc i).col, ∀ π ∈ D.nd.Zgood i, ∃ (hu : u ∈ placesOver D.host.E (D.nd.l i)) (s : ℕ)
      (hs : Good (D.nbr i u hu).Kw s (D.nbr i u hu).LL)
      (hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i (X.ρ i) π).comp (decS D.nd u))) g v),
      IsCrys ((D.loc (D.nd.l i)).PD (D.nbr i u hu).Kw) (wLat D i (X.ρ i) π u hu hc).ρ ∧
      (∀ a ∈ Formalism.MainNotions.LocalSituation.Jset (Formalism.MainNotions.LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i u hu).Kw s
        (D.nbr i u hu).LL hs) (wLat D i (X.ρ i) π u hu hc), -(M0 : ℤ) ≤ a ∧ a ≤ h0) ∧
      ∃ τ, ¬ IsJumpV ((D.loc (D.nd.l i)).PD (D.nbr i u hu).Kw) (wLat D i (X.ρ i) π u hu hc).ρ τ 0 ∧
        Formalism.MainNotions.LocalSituation.c0 (Formalism.MainNotions.LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i u hu).Kw s (D.nbr i u hu).LL hs)
          (wLat D i (X.ρ i) π u hu hc) τ M0 h0 ≤ X.c0 i u

end Formalism.MainNotions.N
