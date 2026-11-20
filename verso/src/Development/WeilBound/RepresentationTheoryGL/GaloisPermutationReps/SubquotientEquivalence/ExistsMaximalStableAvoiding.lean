import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

section Quot

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def subRep4 (π : Representation ℂ G V) (U : Submodule ℂ V) (hU : ∀ g, ∀ v ∈ U, π g v ∈ U) :
    Representation ℂ G U where
  toFun g := (π g).restrict (fun v hv => hU g v hv)
  map_one' := LinearMap.ext fun v => Subtype.ext (by
    show π 1 (v : V) = v
    rw [map_one]; rfl)
  map_mul' g h := LinearMap.ext fun v => Subtype.ext (by
    show π (g * h) (v : V) = π g (π h v)
    rw [map_mul]; rfl)

def quotRep4 (π : Representation ℂ G V) (M : Submodule ℂ V) (hM : ∀ g, ∀ v ∈ M, π g v ∈ M) :
    Representation ℂ G (V ⧸ M) where
  toFun g := M.mapQ M (π g) (fun v hv => hM g v hv)
  map_one' := LinearMap.ext fun x => Submodule.Quotient.induction_on M x fun v => by
    show Submodule.Quotient.mk (π 1 v) = Submodule.Quotient.mk v
    rw [map_one]; rfl
  map_mul' g h := LinearMap.ext fun x => Submodule.Quotient.induction_on M x fun v => by
    show Submodule.Quotient.mk (π (g * h) v) = Submodule.Quotient.mk (π g (π h v))
    rw [map_mul]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem quotRep4_mk (π : Representation ℂ G V) (M : Submodule ℂ V) (hM : ∀ g, ∀ v ∈ M, π g v ∈ M) (g : G) (v : V) :
    quotRep4 π M hM g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π g v) := rfl

/- English proof (translation)
Set `S : Set (Submodule ℂ V)` to `{N | (∀ g, ∀ v ∈ N, π g v ∈ N) ∧ x₀ ∉ N}`. Establish `hbot : (⊥ : Submodule ℂ V) ∈ S` using `⟨fun g v hv => by`. Rewrite using `[(Submodule.mem_bot ℂ).1 hv, map_zero]`. Conclude with `Submodule.zero_mem _, fun h => hx₀ ((Submodule.mem_bot ℂ).1 h)⟩`. Take `⟨M, -, hMS, hMmax⟩` from `zorn_le_nonempty₀ S (fun c hcS hc y hy => by`.

Establish `hne : c.Nonempty` using `⟨y, hy⟩`. Establish `hdir : DirectedOn (· ≤ ·) c` using `hc.directedOn`. Use `⟨sSup c, ⟨fun g v hv => ?_, fun h => ?_⟩, fun z hz => le_sSup hz⟩` and prove the remaining obligations. Take `⟨N, hN, hvN⟩` from `(Submodule.mem_sSup_of_directed hne hdir).1 hv`. Conclude with `le_sSup hN ((hcS hN).1 g v hvN)`.

Take `⟨N, hN, hxN⟩` from `(Submodule.mem_sSup_of_directed hne hdir).1 h`. Conclude with `(hcS hN).2 hxN) ⊥ hbot`. Conclude with `⟨M, hMS.1, hMS.2, fun N hN hxN hMN => le_antisymm (hMmax ⟨hN, hxN⟩ hMN) hMN⟩`.
-/
theorem exists_maximal_stable_avoiding (π : Representation ℂ G V) (x₀ : V) (hx₀ : x₀ ≠ 0) :
    ∃ M : Submodule ℂ V, (∀ g, ∀ v ∈ M, π g v ∈ M) ∧ x₀ ∉ M ∧
      ∀ N : Submodule ℂ V, (∀ g, ∀ v ∈ N, π g v ∈ N) → x₀ ∉ N → M ≤ N → N = M := by
  let S : Set (Submodule ℂ V) := {N | (∀ g, ∀ v ∈ N, π g v ∈ N) ∧ x₀ ∉ N}
  have hbot : (⊥ : Submodule ℂ V) ∈ S := ⟨fun g v hv => by
    rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact Submodule.zero_mem _, fun h => hx₀ ((Submodule.mem_bot ℂ).1 h)⟩
  obtain ⟨M, -, hMS, hMmax⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨fun g v hv => ?_, fun h => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨N, hN, hvN⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hv
      exact le_sSup hN ((hcS hN).1 g v hvN)
    · obtain ⟨N, hN, hxN⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 h
      exact (hcS hN).2 hxN) ⊥ hbot
  exact ⟨M, hMS.1, hMS.2, fun N hN hxN hMN => le_antisymm (hMmax ⟨hN, hxN⟩ hMN) hMN⟩

/- English proof (translation)
Establish `hne : (Submodule.Quotient.mk x₀ : V ⧸ M) ≠ 0`. Rewrite using `[Ne, Submodule.Quotient.mk_eq_zero]` and apply the resulting hypothesis. Use `{ toNontrivial := ⟨⊥, ⊤, fun h => hne ?_⟩, eq_bot_or_eq_top := fun S => ?_ }` and prove the remaining obligations. Establish `h1 : (Submodule.Quotient.mk x₀ : V ⧸ M) ∈ (⊤ : Subrepresentation (quotRep4 π M hM)).toSubmodule` using `Submodule.mem_top`. Rewrite `h1` using `[← h]`.

Conclude with `(Submodule.mem_bot ℂ).1 h1`. Set `N : Submodule ℂ V` to `S.toSubmodule.comap M.mkQ`. Establish `hNst : ∀ g, ∀ v ∈ N, π g v ∈ N` using `fun g v hv => by show Submodule.Quotient.mk (π g v) ∈ S.toSubmodule`. Rewrite using `[← quotRep4_mk π M hM]`. Conclude with `S.apply_mem_toSubmodule g hv`.

Distinguish the cases in `hx : x₀ ∈ N`. Use `right`. Establish `hN` using `hgen N hNst hx`. Use `Subrepresentation.ext (eq_top_iff.2 fun q _ => ?_)` and prove the remaining obligations. Proceed by induction on `q using Submodule.Quotient.induction_on with`.

Consider the case `H v`. Establish `: v ∈ N` using `by rw [hN]; exact Submodule.mem_top`. Conclude with `this`. Use `left`. Establish `hMN : M ≤ N` using `fun v hv => by show Submodule.Quotient.mk v ∈ S.toSubmodule`.

Rewrite using `[(Submodule.Quotient.mk_eq_zero M).2 hv]`. Conclude with `Submodule.zero_mem _`. Establish `hN` using `hmax N hNst hx hMN`. Use `Subrepresentation.ext (eq_bot_iff.2 fun q hq => ?_)` and prove the remaining obligations. Proceed by induction on `q using Submodule.Quotient.induction_on with`.

Consider the case `H v`. Establish `: v ∈ N` using `hq`. Rewrite `this` using `[hN]`. Conclude with `(Submodule.mem_bot ℂ).2 ((Submodule.Quotient.mk_eq_zero M).2 this)`.
-/
theorem quotRep4_irr (π : Representation ℂ G V) (M : Submodule ℂ V) (hM : ∀ g, ∀ v ∈ M, π g v ∈ M) (x₀ : V)
    (hgen : ∀ N : Submodule ℂ V, (∀ g, ∀ v ∈ N, π g v ∈ N) → x₀ ∈ N → N = ⊤) (hx₀ : x₀ ∉ M)
    (hmax : ∀ N : Submodule ℂ V, (∀ g, ∀ v ∈ N, π g v ∈ N) → x₀ ∉ N → M ≤ N → N = M) :
    (quotRep4 π M hM).IsIrreducible := by
  have hne : (Submodule.Quotient.mk x₀ : V ⧸ M) ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  refine { toNontrivial := ⟨⊥, ⊤, fun h => hne ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h1 : (Submodule.Quotient.mk x₀ : V ⧸ M) ∈ (⊤ : Subrepresentation (quotRep4 π M hM)).toSubmodule :=
      Submodule.mem_top
    rw [← h] at h1
    exact (Submodule.mem_bot ℂ).1 h1
  · let N : Submodule ℂ V := S.toSubmodule.comap M.mkQ
    have hNst : ∀ g, ∀ v ∈ N, π g v ∈ N := fun g v hv => by
      show Submodule.Quotient.mk (π g v) ∈ S.toSubmodule
      rw [← quotRep4_mk π M hM]
      exact S.apply_mem_toSubmodule g hv
    by_cases hx : x₀ ∈ N
    · right
      have hN := hgen N hNst hx
      refine Subrepresentation.ext (eq_top_iff.2 fun q _ => ?_)
      induction q using Submodule.Quotient.induction_on with
      | H v =>
        have : v ∈ N := by rw [hN]; exact Submodule.mem_top
        exact this
    · left
      have hMN : M ≤ N := fun v hv => by
        show Submodule.Quotient.mk v ∈ S.toSubmodule
        rw [(Submodule.Quotient.mk_eq_zero M).2 hv]
        exact Submodule.zero_mem _
      have hN := hmax N hNst hx hMN
      refine Subrepresentation.ext (eq_bot_iff.2 fun q hq => ?_)
      induction q using Submodule.Quotient.induction_on with
      | H v =>
        have : v ∈ N := hq
        rw [hN] at this
        exact (Submodule.mem_bot ℂ).2 ((Submodule.Quotient.mk_eq_zero M).2 this)

end Quot

/- English proof (translation)
Take `⟨π₀, hπ₀⟩` from `exists_uniformizer k`. Establish `h1 : ord k π₀ = 1` using `ord_eq_one hπ₀`. Establish `h0 : ord k π₀⁻¹ = -1`. Use `ord_mul k π₀ π₀⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, ord_eq_zero (by simp), h1]`.

Use linear arithmetic over natural numbers and integers. Establish `h2 : ord k (ϖ * π₀⁻¹) = 0` using `by rw [ord_mul, h0, hϖ]; norm_num`. Establish `h3` using `ord_eq_zero_iff.1 h2`. Rewrite `h3` using `[Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]`. Establish `hne : valuation k (π₀ : k) ≠ 0` using `by simp`.

Rewrite `h3` using `[mul_inv_eq_one₀ hne]`. Rewrite using `[h3, hπ₀]`.
-/
theorem val_unif4 {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ϖ : kˣ}
    (hϖ : ord k ϖ = 1) : valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨π₀, hπ₀⟩ := exists_uniformizer k
  have h1 : ord k π₀ = 1 := ord_eq_one hπ₀
  have h0 : ord k π₀⁻¹ = -1 := by
    have := ord_mul k π₀ π₀⁻¹
    rw [mul_inv_cancel, ord_eq_zero (by simp), h1] at this
    omega
  have h2 : ord k (ϖ * π₀⁻¹) = 0 := by rw [ord_mul, h0, hϖ]; norm_num
  have h3 := ord_eq_zero_iff.1 h2
  rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀] at h3
  have hne : valuation k (π₀ : k) ≠ 0 := by simp
  rw [mul_inv_eq_one₀ hne] at h3
  rw [h3, hπ₀]

/- English proof (translation)
Introduce `k W _ _ _ _ _ _ _ n hn τ hτ ϖ hϖ c`. Use `haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩`. Take `⟨ω₀, hω₀⟩` from `exists_hasCentralChar hτ`. Take `⟨ω, hω, hωc⟩` from `exists_isTameLift ω₀ (val_unif4 hϖ) c`. Establish `hE : ExtendsCentral ω τ` using `hω.extendsCentral hω₀`.

Choose the witnesses or unpack the hypotheses as in `⟨w₀, hw₀⟩ : ∃ w₀ : W, w₀ ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Use `haveI := hτ`. Conclude with `(bot_ne_top : (⊥ : Subrepresentation τ) ≠ ⊤) (Subrepresentation.ext (Submodule.ext fun w => by`.

Rewrite using `[hcon w]`. Conclude with `⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩))`. Set `π₀` to `depthZero τ ω hE`. Set `cn` to `canon τ ω hE`. Establish `hcn : ∀ (g : KO k (Fin n)) (w : W), cn (τ (redK k (Fin n) g) w) = π₀ g (cn w)` using `fun g w => by`.

Rewrite using `[← extZK_KO τ ω hE, (canon τ ω hE).isIntertwining]`. Both sides reduce to the same expression. Set `x₀` to `cn w₀`. Establish `hx₀ : x₀ ≠ 0` using `fun h => hw₀ (canon_injective τ ω hE (h.trans (map_zero _).symm))`. Set `U : Submodule ℂ (DepthZeroSp τ ω hE)` to `Submodule.span ℂ (Set.range fun g => π₀ g x₀)`.

Establish `hU : ∀ g, ∀ v ∈ U, π₀ g v ∈ U` using `fun g v hv => by`. Establish `hle : U ≤ U.comap (π₀ g)` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨h, rfl⟩`. Conclude with `Submodule.subset_span ⟨g * h, by simp only [map_mul, Module.End.mul_apply]⟩)`. Conclude with `hle hv`.

Establish `hx₀U : x₀ ∈ U` using `Submodule.subset_span ⟨1, by simp only [map_one, Module.End.one_apply]⟩`. Establish `hcnU : ∀ w, cn w ∈ U`. Set `S : Subrepresentation τ` to `⟨U.comap cn.toLinearMap, fun g v hv => by`. Take `⟨g', rfl⟩` from `redK_surjective g`. Use `show cn _ ∈ U`.

Rewrite using `[hcn]`. Conclude with `hU g' _ hv⟩`. Establish `hS : S = ⊤`. Use `(hτ.eq_bot_or_eq_top S).resolve_left fun h => hw₀ ?_` and prove the remaining obligations. Establish `: w₀ ∈ S.toSubmodule` using `hx₀U`.

Rewrite `this` using `[h]`. Conclude with `(Submodule.mem_bot ℂ).1 this`. Introduce `w`. Establish `: w ∈ S.toSubmodule` using `by rw [hS]; exact Submodule.mem_top`. Conclude with `this`.

Set `π₁` to `subRep4 π₀ U hU`. Set `x₁ : U` to `⟨x₀, hx₀U⟩`. Establish `hx₁ : x₁ ≠ 0` using `fun h => hx₀ (congrArg Subtype.val h)`. Establish `hgen : ∀ N : Submodule ℂ U, (∀ g, ∀ v ∈ N, π₁ g v ∈ N) → x₁ ∈ N → N = ⊤`. Introduce `N hN hxN`.

Establish `hle : U ≤ N.map U.subtype` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `⟨π₁ g x₁, hN g x₁ hxN, rfl⟩)`. Use `eq_top_iff.2 fun u _ => ?_` and prove the remaining obligations. Take `⟨u', hu', he⟩` from `hle u.2`.

Rewrite `hu'` using `[show u' = u from Subtype.ext he]`. Then use the resulting hypothesis. Take `⟨M, hM, hx₁M, hMmax⟩` from `exists_maximal_stable_avoiding π₁ x₁ hx₁`. Set `ρQ` to `quotRep4 π₁ M hM`. Establish `hirr : ρQ.IsIrreducible` using `quotRep4_irr π₁ M hM x₁ hgen hx₁M hMmax`. Establish `hsm : IsSmooth ρQ`.

Introduce `q`. Proceed by induction on `q using Submodule.Quotient.induction_on with`. Consider the case `H u`. Set `H : Subgroup (GL (Fin n) k)` to `{ carrier := {g | ρQ g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u} one_mem' := by simp only [Set.mem_setOf_eq, map_one, Module.End.one_apply] mul_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at ha hb ⊢`.

Rewrite using `[hb, ha]`. Use the proof step `inv_mem' := fun {a} ha => by`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`. Use `conv_lhs => rw [← ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }`.

Establish `hopen : IsOpen {g : GL (Fin n) k | π₀ g (u : DepthZeroSp τ ω hE) = u}` using `isSmooth_depthZero τ ω hE u`. Establish `hsub : {g : GL (Fin n) k | π₀ g (u : DepthZeroSp τ ω hE) = u} ⊆ (H : Set (GL (Fin n) k))` using `fun g hg => by show ρQ g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u`. Rewrite using `[quotRep4_mk]`. Use `congr 1`. Conclude with `Subtype.ext hg`.

Conclude with `Subgroup.isOpen_of_mem_nhds H (g := 1) (Filter.mem_of_superset (hopen.mem_nhds (by simp only [Set.mem_setOf_eq, map_one, Module.End.one_apply])) hsub)`. Set `jU : W →ₗ[ℂ] U` to `LinearMap.codRestrict U cn.toLinearMap hcnU`. Set `j : W →ₗ[ℂ] (U ⧸ M)` to `M.mkQ.comp jU`. Establish `hj : ∀ (g : KO k (Fin n)) (v : W), j (τ (redK k (Fin n) g) v) = ρQ g (j v)` using `fun g v => by show Submodule.Quotient.mk (jU (τ (redK k (Fin n) g) v)) = Submodule.Quotient.mk (π₁ g (jU v))`. Use `congr 1`.

Conclude with `Subtype.ext (hcn g v)`. Establish `hjinj : Function.Injective j`. Set `K : Subrepresentation τ` to `⟨LinearMap.ker j, fun g v hv => by`. Take `⟨g', rfl⟩` from `redK_surjective g`. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`.

Rewrite using `[hj, hv, map_zero]⟩`. Establish `hK : K = ⊥`. Use `(hτ.eq_bot_or_eq_top K).resolve_right fun h => ?_` and prove the remaining obligations. Establish `: w₀ ∈ K.toSubmodule` using `by rw [h]; exact Submodule.mem_top`. Establish `h2 : j w₀ = 0` using `LinearMap.mem_ker.1 this`.

Apply `hx₁M` to reduce the goal to its premises. Conclude with `(Submodule.Quotient.mk_eq_zero M).1 h2`. Establish `: LinearMap.ker j = ⊥` using `congrArg Subrepresentation.toSubmodule hK`. Conclude with `LinearMap.ker_eq_bot.1 this`. Use `⟨⟨U ⧸ M, ρQ, hsm, hirr⟩, ω, j, ?_, hωc, hjinj, hj⟩` and prove the remaining obligations.

Introduce `z q`. Proceed by induction on `q using Submodule.Quotient.induction_on with`. Consider the case `H u => show ρQ (GeneralLinearGroup.scalar (Fin n) z) (Submodule.Quotient.mk u) = (ω z : ℂ) • Submodule.Quotient.mk u`. Rewrite using `[quotRep4_mk, ← Submodule.Quotient.mk_smul]`. Use `congr 1`.

Conclude with `Subtype.ext (hasCentralChar_depthZero τ ω hE z u)`.
-/
theorem st4 : St4 := by
  intro k W _ _ _ _ _ _ _ n hn τ hτ ϖ hϖ c
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨ω₀, hω₀⟩ := exists_hasCentralChar hτ
  obtain ⟨ω, hω, hωc⟩ := exists_isTameLift ω₀ (val_unif4 hϖ) c
  have hE : ExtendsCentral ω τ := hω.extendsCentral hω₀
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : W, w₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    haveI := hτ
    exact (bot_ne_top : (⊥ : Subrepresentation τ) ≠ ⊤) (Subrepresentation.ext (Submodule.ext fun w => by
      rw [hcon w]; exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩))
  let π₀ := depthZero τ ω hE
  let cn := canon τ ω hE
  have hcn : ∀ (g : KO k (Fin n)) (w : W), cn (τ (redK k (Fin n) g) w) = π₀ g (cn w) := fun g w => by
    rw [← extZK_KO τ ω hE, (canon τ ω hE).isIntertwining]; rfl
  let x₀ := cn w₀
  have hx₀ : x₀ ≠ 0 := fun h => hw₀ (canon_injective τ ω hE (h.trans (map_zero _).symm))
  let U : Submodule ℂ (DepthZeroSp τ ω hE) := Submodule.span ℂ (Set.range fun g => π₀ g x₀)
  have hU : ∀ g, ∀ v ∈ U, π₀ g v ∈ U := fun g v hv => by
    have hle : U ≤ U.comap (π₀ g) := Submodule.span_le.2 (by
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp only [map_mul, Module.End.mul_apply]⟩)
    exact hle hv
  have hx₀U : x₀ ∈ U := Submodule.subset_span ⟨1, by simp only [map_one, Module.End.one_apply]⟩
  have hcnU : ∀ w, cn w ∈ U := by
    let S : Subrepresentation τ := ⟨U.comap cn.toLinearMap, fun g v hv => by
      obtain ⟨g', rfl⟩ := redK_surjective g
      show cn _ ∈ U
      rw [hcn]
      exact hU g' _ hv⟩
    have hS : S = ⊤ := by
      refine (hτ.eq_bot_or_eq_top S).resolve_left fun h => hw₀ ?_
      have : w₀ ∈ S.toSubmodule := hx₀U
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    intro w
    have : w ∈ S.toSubmodule := by rw [hS]; exact Submodule.mem_top
    exact this
  let π₁ := subRep4 π₀ U hU
  let x₁ : U := ⟨x₀, hx₀U⟩
  have hx₁ : x₁ ≠ 0 := fun h => hx₀ (congrArg Subtype.val h)
  have hgen : ∀ N : Submodule ℂ U, (∀ g, ∀ v ∈ N, π₁ g v ∈ N) → x₁ ∈ N → N = ⊤ := by
    intro N hN hxN
    have hle : U ≤ N.map U.subtype := Submodule.span_le.2 (by
      rintro _ ⟨g, rfl⟩
      exact ⟨π₁ g x₁, hN g x₁ hxN, rfl⟩)
    refine eq_top_iff.2 fun u _ => ?_
    obtain ⟨u', hu', he⟩ := hle u.2
    rwa [show u' = u from Subtype.ext he] at hu'
  obtain ⟨M, hM, hx₁M, hMmax⟩ := exists_maximal_stable_avoiding π₁ x₁ hx₁
  let ρQ := quotRep4 π₁ M hM
  have hirr : ρQ.IsIrreducible := quotRep4_irr π₁ M hM x₁ hgen hx₁M hMmax
  have hsm : IsSmooth ρQ := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H u =>
      let H : Subgroup (GL (Fin n) k) :=
        { carrier := {g | ρQ g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u}
          one_mem' := by simp only [Set.mem_setOf_eq, map_one, Module.End.one_apply]
          mul_mem' := fun {a b} ha hb => by
            simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at ha hb ⊢
            rw [hb, ha]
          inv_mem' := fun {a} ha => by
            simp only [Set.mem_setOf_eq] at ha ⊢
            conv_lhs => rw [← ha]
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
      have hopen : IsOpen {g : GL (Fin n) k | π₀ g (u : DepthZeroSp τ ω hE) = u} := isSmooth_depthZero τ ω hE u
      have hsub : {g : GL (Fin n) k | π₀ g (u : DepthZeroSp τ ω hE) = u} ⊆ (H : Set (GL (Fin n) k)) := fun g hg => by
        show ρQ g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u
        rw [quotRep4_mk]
        congr 1
        exact Subtype.ext hg
      exact Subgroup.isOpen_of_mem_nhds H (g := 1)
        (Filter.mem_of_superset (hopen.mem_nhds (by simp only [Set.mem_setOf_eq, map_one, Module.End.one_apply])) hsub)
  let jU : W →ₗ[ℂ] U := LinearMap.codRestrict U cn.toLinearMap hcnU
  let j : W →ₗ[ℂ] (U ⧸ M) := M.mkQ.comp jU
  have hj : ∀ (g : KO k (Fin n)) (v : W), j (τ (redK k (Fin n) g) v) = ρQ g (j v) := fun g v => by
    show Submodule.Quotient.mk (jU (τ (redK k (Fin n) g) v)) = Submodule.Quotient.mk (π₁ g (jU v))
    congr 1
    exact Subtype.ext (hcn g v)
  have hjinj : Function.Injective j := by
    let K : Subrepresentation τ := ⟨LinearMap.ker j, fun g v hv => by
      obtain ⟨g', rfl⟩ := redK_surjective g
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hj, hv, map_zero]⟩
    have hK : K = ⊥ := by
      refine (hτ.eq_bot_or_eq_top K).resolve_right fun h => ?_
      have : w₀ ∈ K.toSubmodule := by rw [h]; exact Submodule.mem_top
      have h2 : j w₀ = 0 := LinearMap.mem_ker.1 this
      apply hx₁M
      exact (Submodule.Quotient.mk_eq_zero M).1 h2
    have : LinearMap.ker j = ⊥ := congrArg Subrepresentation.toSubmodule hK
    exact LinearMap.ker_eq_bot.1 this
  refine ⟨⟨U ⧸ M, ρQ, hsm, hirr⟩, ω, j, ?_, hωc, hjinj, hj⟩
  intro z q
  induction q using Submodule.Quotient.induction_on with
  | H u =>
    show ρQ (GeneralLinearGroup.scalar (Fin n) z) (Submodule.Quotient.mk u) = (ω z : ℂ) • Submodule.Quotient.mk u
    rw [quotRep4_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (hasCentralChar_depthZero τ ω hE z u)

end PositivityTheory.Rg.DzCount

end
