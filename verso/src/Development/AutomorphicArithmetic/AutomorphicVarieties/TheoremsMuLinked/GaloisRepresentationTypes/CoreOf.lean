import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdVan2
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.RegDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.PolNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.RedBChiComap
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CharacteristicPolynomials.EpsDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RelKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `_ = (ρ g : Matrix (Fin n) (Fin n) K) * X * (ρ g⁻¹ : GL (Fin n) K)`. Rewrite using `[map_inv]`. Both sides reduce to the same expression.
-/
private theorem ad_eq {H K : Type} [Group H] [CommRing K] {n : ℕ} (ρ : H →* GL (Fin n) K) (g : H) (X : Matrix (Fin n) (Fin n) K) :
    Loc.adGL ρ g X = W.mat ρ g * X * W.mat ρ g⁻¹ := by
  change _ = (ρ g : Matrix (Fin n) (Fin n) K) * X * (ρ g⁻¹ : GL (Fin n) K)
  rw [map_inv]
  rfl

/- English proof (translation)
The claim follows from `hy.sub (((ha.matrix_mul continuous_const).matrix_mul (ha.comp continuous_inv)).sub continuous_const)`.
-/
private theorem cont_sub {H K : Type} [Group H] [TopologicalSpace H] [ContinuousInv H] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {n : ℕ} {a y : H → Matrix (Fin n) (Fin n) K} (ha : Continuous a) (hy : Continuous y)
    (X : Matrix (Fin n) (Fin n) K) : Continuous fun g => y g - (a g * X * a g⁻¹ - X) :=
  hy.sub (((ha.matrix_mul continuous_const).matrix_mul (ha.comp continuous_inv)).sub continuous_const)

/- English proof (translation)
Introduce `hO hΦ l _ L Ω _ _ _ _ _ _ s V hV _ c _ n h2 h4 r h0 B ι x ρ hN P R hP hR z hz hzo`. Take `⟨h, hh⟩` from `hN.arith`. Take `⟨hD, -⟩` from `Det.redB x ρ hN.rep`. Establish `hfull : Submodule.span (Qbar l) (Set.range (W.mat ρ)) = ⊤` using `KStar.Schema.span_eq_top_of_irreducible _ fun N hs => hN.irr N fun g _ => hs g`. Establish `hI` using `(Ws.Eb.relKill B x ρ hfull hD).2`.

Take `⟨X₀, hpol, hext⟩` from `Det.polNorm V.frame ρ P R z hR hz.2`. Establish `heps : ∃ g : V.frame.G₀, V.frame.ε g ≠ 1`. Take `⟨g, -, hg⟩` from `h0.2.2`. Use `⟨g, fun e => hg ?_⟩` and prove the remaining obligations. Establish `e' : (V.frame.ε.comp V.frame.η.ker.subtype) g = 1` using `e`.

Rewrite using `[W.GFrame.eps, MonoidHom.comp_apply, e', map_one]`. Establish `hdet` using `regDet V.frame c.O ρ P (by omega) (hΦ l L Ω s V).2.1 heps hN.cont hN.irr hN.n3`. Establish `hno : ∀ (v : W.Vl l L) i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F` using `L) (s.A v)).subtype := by`. Introduce `v i j e`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Establish `h1` using `(s.hA v.1 ((l : ℕ) : 𝓞 (W.Lp L))).2 v.2`. Conclude with `Det.epsDec (s.A v.1) (s.w v.1) (s.hw v.1) ((s.hw v.1 _).1 (by simpa using h1)) (left_eq_mul.1 e)`. Take `⟨g, hg, hf⟩` from `hN.free v`. Use `hf i j hij 1 one_pos ?_` and prove the remaining obligations.

Establish `e1 : V.ε (toGS Ω V.S' (W.resP L Ω (Subtype.val g))) = cycZ (W.Lp L) Ω l (W.resP L Ω (Subtype.val g))` using `DFunLike.congr_fun V.hε _`. Establish `e2 : cycZ L Ω l (Subtype.val g) = 1` using `e1.symm.trans hg`. Establish `e3 : cycBar L Ω l (Subtype.val g) = 1` using `by rw [cycBar, MonoidHom.comp_apply, e2, map_one]`. Establish `e4 : x.psi v i g = x.psi v j g * cycBar L Ω l (Subtype.val g)` using `DFunLike.congr_fun e g`. Rewrite `e4` using `[e3, mul_one]`.

Simplify using `only [pow_one]`. Conclude with `e4`. Establish `hc : Continuous fun g : V.frame.G₀ => W.mat ρ g` using `Units.continuous_val.comp hN.cont`. Use `(hO l L Ω s V c n r B ι x h ρ P hV h2 h4 h0 hh hD hN.cont hN.aut hfull hP hN.unr0 hno hdet (fun g => z g - Pa.dY V.frame (W.mat ρ) X₀ g) ⟨?_, fun g g' => ?_, hpol, fun u g hg => ?_, fun v => ?_⟩).elim hext` and prove the remaining obligations. Conclude with `cont_sub hc (hz.1.comp continuous_subtype_val) X₀`.

Establish `e1 : z ((g * g' : V.frame.G₀) : V.frame.Γ) = z g + W.mat ρ g * z g' * W.mat ρ g⁻¹`. Rewrite using `[← ad_eq, ← hR.ad]`. Conclude with `hz.2 _ _`. Establish `e2 : W.mat ρ g * W.mat ρ g⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Simplify using `only [e1, Pa.dY, _root_.mul_inv_rev, map_mul]`.

Use `noncomm_ring`. Simplify using `only [hzo.ine u g hg, Pa.dY, W.mat, MonoidHom.comp_apply, map_inv, hI u g hg]`. Simplify using the standard rewrite rules. Take `⟨a, X, ha⟩` from `hzo.ord v`. Use `⟨a⁻¹, X - X₀, fun g => ?_⟩` and prove the remaining obligations.

Take `⟨a1, a2, a3, a4⟩` from `ha g`. Establish `e : z (V.frame.φ v g) - Pa.dY V.frame (W.mat ρ) X₀ (V.frame.φ v g) - Pa.dY V.frame (W.mat ρ) (X - X₀) (V.frame.φ v g) = z (V.frame.φ v g) - (Loc.adGL (ρ.comp (V.frame.φ v)) g X - X)`. Rewrite using `[ad_eq]`. Establish `e1 : ∀ t, W.mat (ρ.comp (V.frame.φ v)) t = W.mat ρ (V.frame.φ v t)` using `fun _ => rfl`. Simplify using `only [Pa.dY, e1, map_inv]`.

Use `noncomm_ring`. Rewrite using `[inv_inv, e]`. Conclude with `⟨a1, a2, a3, a4⟩`.
-/
theorem UpperTheory.V.Th.core_of :
    Th.OrdVan2 → W.PhiAll → Th.Core := by
  intro hO hΦ l _ L Ω _ _ _ _ _ _ s V hV _ c _ n h2 h4 r h0 B ι x ρ hN P R hP hR z hz hzo
  obtain ⟨h, hh⟩ := hN.arith
  obtain ⟨hD, -⟩ := Det.redB x ρ hN.rep
  have hfull : Submodule.span (Qbar l) (Set.range (W.mat ρ)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun N hs => hN.irr N fun g _ => hs g
  have hI := (Ws.Eb.relKill B x ρ hfull hD).2
  obtain ⟨X₀, hpol, hext⟩ := Det.polNorm V.frame ρ P R z hR hz.2
  have heps : ∃ g : V.frame.G₀, V.frame.ε g ≠ 1 := by
    obtain ⟨g, -, hg⟩ := h0.2.2
    refine ⟨g, fun e => hg ?_⟩
    have e' : (V.frame.ε.comp V.frame.η.ker.subtype) g = 1 := e
    rw [W.GFrame.eps, MonoidHom.comp_apply, e', map_one]
  have hdet := regDet V.frame c.O ρ P (by omega) (hΦ l L Ω s V).2.1 heps hN.cont hN.irr hN.n3
  have hno : ∀ (v : W.Vl l L) i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype := by
    intro v i j e
    by_cases hij : i = j
    · subst hij
      have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (W.Lp L))).2 v.2
      exact Det.epsDec (s.A v.1) (s.w v.1) (s.hw v.1) ((s.hw v.1 _).1 (by simpa using h1)) (left_eq_mul.1 e)
    · obtain ⟨g, hg, hf⟩ := hN.free v
      refine hf i j hij 1 one_pos ?_
      have e1 : V.ε (toGS Ω V.S' (W.resP L Ω (Subtype.val g))) = cycZ (W.Lp L) Ω l (W.resP L Ω (Subtype.val g)) :=
        DFunLike.congr_fun V.hε _
      have e2 : cycZ L Ω l (Subtype.val g) = 1 := e1.symm.trans hg
      have e3 : cycBar L Ω l (Subtype.val g) = 1 := by rw [cycBar, MonoidHom.comp_apply, e2, map_one]
      have e4 : x.psi v i g = x.psi v j g * cycBar L Ω l (Subtype.val g) := DFunLike.congr_fun e g
      rw [e3, mul_one] at e4
      simp only [pow_one]
      exact e4
  have hc : Continuous fun g : V.frame.G₀ => W.mat ρ g := Units.continuous_val.comp hN.cont
  refine (hO l L Ω s V c n r B ι x h ρ P hV h2 h4 h0 hh hD hN.cont hN.aut hfull hP hN.unr0 hno hdet
    (fun g => z g - Pa.dY V.frame (W.mat ρ) X₀ g) ⟨?_, fun g g' => ?_, hpol, fun u g hg => ?_, fun v => ?_⟩).elim hext
  · exact cont_sub hc (hz.1.comp continuous_subtype_val) X₀
  · have e1 : z ((g * g' : V.frame.G₀) : V.frame.Γ) = z g + W.mat ρ g * z g' * W.mat ρ g⁻¹ := by
      rw [← ad_eq, ← hR.ad]
      exact hz.2 _ _
    have e2 : W.mat ρ g * W.mat ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    simp only [e1, Pa.dY, _root_.mul_inv_rev, map_mul]
    noncomm_ring
  · simp only [hzo.ine u g hg, Pa.dY, W.mat, MonoidHom.comp_apply, map_inv, hI u g hg]
    simp
  · obtain ⟨a, X, ha⟩ := hzo.ord v
    refine ⟨a⁻¹, X - X₀, fun g => ?_⟩
    obtain ⟨a1, a2, a3, a4⟩ := ha g
    have e : z (V.frame.φ v g) - Pa.dY V.frame (W.mat ρ) X₀ (V.frame.φ v g) - Pa.dY V.frame (W.mat ρ) (X - X₀) (V.frame.φ v g) =
        z (V.frame.φ v g) - (Loc.adGL (ρ.comp (V.frame.φ v)) g X - X) := by
      rw [ad_eq]
      have e1 : ∀ t, W.mat (ρ.comp (V.frame.φ v)) t = W.mat ρ (V.frame.φ v t) := fun _ => rfl
      simp only [Pa.dY, e1, map_inv]
      noncomm_ring
    rw [inv_inv, e]
    exact ⟨a1, a2, a3, a4⟩
