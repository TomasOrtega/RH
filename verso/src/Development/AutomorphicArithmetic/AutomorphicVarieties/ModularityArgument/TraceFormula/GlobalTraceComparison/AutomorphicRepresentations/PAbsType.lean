import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TwtrContOfMem

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

/- English proof (translation)
Set `core : InnerProductSpace.Core ℂ F` to `{ inner := fun a b => B a b conj_inner_symm := fun a b => hsym b a re_inner_nonneg := fun a => by`. Distinguish the cases in `h : a = 0`. Simplify using `[h]`. Conclude with `(hpos a h).le`. Use `add_left := fun a b c => by simp`.

Use `smul_left := fun a b r => by simp`. Use `definite := fun a h => by`. Assume the negation of the conclusion as `h0`. Establish `h1` using `hpos a h0`. Establish `h2 : B a a = 0` using `h`.

Simplify using `[h2] at h1 }`. Use `letI : NormedAddCommGroup F := core.toNormedAddCommGroup`. Use `letI : InnerProductSpace ℂ F := InnerProductSpace.ofCore core.toCore`. Use `haveI : CompleteSpace S := FiniteDimensional.complete ℂ S`. Use `⟨S.starProjection.toLinearMap, fun x => S.starProjection_apply_mem x, fun x a ha => ?_⟩` and prove the remaining obligations.

Establish `h0` using `S.starProjection_inner_eq_zero x a ha`. Establish `h1 : B (x - S.starProjection x) a = 0` using `h0`. Establish `h2` using `hsym (x - S.starProjection x) a`. Rewrite `h2` using `[h1, map_zero]`. Conclude with `h2.symm`.
-/
private lemma exists_projL {F : Type} [AddCommGroup F] [Module ℂ F] (B : F →ₗ⋆[ℂ] F →ₗ[ℂ] ℂ)
    (hsym : ∀ a b, starRingEnd ℂ (B a b) = B b a) (hpos : ∀ a, a ≠ 0 → 0 < (B a a).re)
    (S : Submodule ℂ F) [FiniteDimensional ℂ S] :
    ∃ P : F →ₗ[ℂ] F, (∀ x, P x ∈ S) ∧ ∀ x, ∀ a ∈ S, B a (x - P x) = 0 := by
  let core : InnerProductSpace.Core ℂ F :=
    { inner := fun a b => B a b
      conj_inner_symm := fun a b => hsym b a
      re_inner_nonneg := fun a => by
        by_cases h : a = 0
        · simp [h]
        · exact (hpos a h).le
      add_left := fun a b c => by simp
      smul_left := fun a b r => by simp
      definite := fun a h => by
        by_contra h0
        have h1 := hpos a h0
        have h2 : B a a = 0 := h
        simp [h2] at h1 }
  letI : NormedAddCommGroup F := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ F := InnerProductSpace.ofCore core.toCore
  haveI : CompleteSpace S := FiniteDimensional.complete ℂ S
  refine ⟨S.starProjection.toLinearMap, fun x => S.starProjection_apply_mem x, fun x a ha => ?_⟩
  have h0 := S.starProjection_inner_eq_zero x a ha
  have h1 : B (x - S.starProjection x) a = 0 := h0
  have h2 := hsym (x - S.starProjection x) a
  rw [h1, map_zero] at h2
  exact h2.symm

/- English proof (translation)
Introduce `a ha`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem a h`. Take `⟨k, rfl⟩` from `h`. Use `Submodule.subset_span ⟨g * k, ?_⟩` and prove the remaining obligations.

Simplify using `[map_mul, Module.End.mul_apply]`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul c a _ ha => rw [map_smul]`.

Conclude with `Submodule.smul_mem _ c ha`.
-/
private lemma orbit_stable {Γ F : Type} [Group Γ] [AddCommGroup F] [Module ℂ F]
    (R : Representation ℂ Γ F) (x : F) (g : Γ) :
    ∀ a ∈ Submodule.span ℂ (Set.range fun k => R k x),
      R g a ∈ Submodule.span ℂ (Set.range fun k => R k x) := by
  intro a ha
  induction ha using Submodule.span_induction with
  | mem a h =>
    obtain ⟨k, rfl⟩ := h
    refine Submodule.subset_span ⟨g * k, ?_⟩
    simp [map_mul, Module.End.mul_apply]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨1, by simp⟩`.
-/
private lemma self_mem_orbit {Γ F : Type} [Group Γ] [AddCommGroup F] [Module ℂ F]
    (R : Representation ℂ Γ F) (x : F) : x ∈ Submodule.span ℂ (Set.range fun k => R k x) :=
  Submodule.subset_span ⟨1, by simp⟩

/- English proof (translation)
Introduce `Γ F _ _ _ R B W V Y z hsym hpos hinv hW hV hVf hY hYV hzf hzt`. Establish `hRR : ∀ k a, R k (R k⁻¹ a) = a` using `fun k a => by`. Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Simplify using the standard rewrite rules. Establish `hadj : ∀ k a b, B a (R k b) = B (R k⁻¹ a) b` using `fun k a b => by`.

Establish `h` using `hinv k (R k⁻¹ a) b`. Rewrite `h` using `[hRR]`. Then use the resulting hypothesis. Set `T : Submodule ℂ F` to `{ carrier := {x | ∀ l : F →ₗ[ℂ] ℂ, (fun k => l (R k x)) ∈ W} add_mem' := fun {a b} ha hb l => by`. Establish `h` using `W.add_mem (ha l) (hb l)`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `k`. Simplify using the standard rewrite rules. Use the proof step `zero_mem' := fun l => by`. Establish `h` using `W.zero_mem`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `k`. Simplify using the standard rewrite rules. Use the proof step `smul_mem' := fun c x hx l => by`. Establish `h` using `W.smul_mem c (hx l)`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `k`. Simplify using `}`. Establish `hTR : ∀ g, ∀ x ∈ T, R g x ∈ T` using `fun g x hx l => by`. Establish `h` using `hW _ (hx l) g`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `k`. Simplify using `[map_mul, Module.End.mul_apply]`. Use `haveI : FiniteDimensional ℂ Y := hY`. Use `haveI : FiniteDimensional ℂ (V ⊓ T : Submodule ℂ F) := Submodule.finiteDimensional_of_le (S₂ := Y) fun x hx => hYV x hx.1 hx.2`. Take `⟨P, hPm, hPo⟩` from `exists_projL B hsym hpos (V ⊓ T)`.

Use `⟨P z, (hPm z).1, hYV _ (hPm z).1 (hPm z).2, ?_⟩` and prove the remaining obligations. Establish `hz1T : z - P z ∈ T` using `T.sub_mem hzt (hPm z).2`. Establish `hZT : Submodule.span ℂ (Set.range fun k => R k (z - P z)) ≤ T`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`.

Conclude with `hTR k _ hz1T`. Establish `hZperp : ∀ a ∈ V ⊓ T, ∀ w ∈ Submodule.span ℂ (Set.range fun k => R k (z - P z)), B a w = 0`. Introduce `a ha w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w h`.

Take `⟨k, rfl⟩` from `h`. Use `show B a (R k (z - P z)) = 0`. Rewrite using `[hadj]`. Conclude with `hPo z _ ⟨hV _ _ ha.1, hTR _ _ ha.2⟩`. Consider the case `zero => simp`.

Consider the case `add a' b _ _ ha' hb => rw [map_add, ha', hb, add_zero]`. Consider the case `smul c a' _ ha' => rw [map_smul, ha', smul_zero]`. Introduce `v hv`. Use `haveI := hVf v hv`. Take `⟨Q, hQm, hQo⟩` from `exists_projL B hsym hpos (Submodule.span ℂ (Set.range fun k => R k v))`.

Establish `hV0V : Submodule.span ℂ (Set.range fun k => R k v) ≤ V`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `hV k v hv`. Establish `hzero : ∀ d, B d d = 0 → d = 0` using `fun d h => by`.

Assume the negation of the conclusion as `h0`. Establish `h1` using `hpos d h0`. Simplify using `[h] at h1`. Establish `hQR : ∀ g x, Q (R g x) = R g (Q x)` using `fun g x => by`. Establish `hd : Q (R g x) - R g (Q x) ∈ Submodule.span ℂ (Set.range fun k => R k v)` using `Submodule.sub_mem _ (hQm _) (orbit_stable R v g _ (hQm x))`.

Establish `h1` using `hQo (R g x) _ hd`. Establish `h2 : B (Q (R g x) - R g (Q x)) (R g x - R g (Q x)) = 0`. Rewrite using `[← map_sub, hadj]`. Conclude with `hQo x _ (orbit_stable R v g⁻¹ _ hd)`. Establish `h3 : B (Q (R g x) - R g (Q x)) (Q (R g x) - R g (Q x)) = 0`.

Establish `h4 : B (Q (R g x) - R g (Q x)) (Q (R g x) - R g (Q x)) = B (Q (R g x) - R g (Q x)) (R g x - R g (Q x)) - B (Q (R g x) - R g (Q x)) (R g x - Q (R g x))`. Rewrite using `[← map_sub]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Rewrite using `[h4, h1, h2, sub_zero]`.

Conclude with `sub_eq_zero.1 (hzero _ h3)`. Establish `hQT : ∀ w ∈ Submodule.span ℂ (Set.range fun k => R k (z - P z)), Q w ∈ T` using `fun w hw l => by`. Establish `h` using `hZT hw (l ∘ₗ Q)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k`.

Simplify using `[hQR]`. Establish `hQ0 : Q (z - P z) = 0`. Establish `hw` using `self_mem_orbit R (z - P z)`. Establish `h1` using `hZperp (Q (z - P z)) ⟨hV0V (hQm _), hQT _ hw⟩ _ hw`. Establish `h2` using `hQo (z - P z) _ (hQm (z - P z))`.

Rewrite `h2` using `[map_sub, h1, zero_sub, neg_eq_zero]`. Conclude with `hzero _ h2`. Establish `h` using `hQo (z - P z) v (self_mem_orbit R v)`. Rewrite `h` using `[hQ0, sub_zero]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.absType_pf :
    AbsType := by
  intro Γ F _ _ _ R B W V Y z hsym hpos hinv hW hV hVf hY hYV hzf hzt
  have hRR : ∀ k a, R k (R k⁻¹ a) = a := fun k a => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hadj : ∀ k a b, B a (R k b) = B (R k⁻¹ a) b := fun k a b => by
    have h := hinv k (R k⁻¹ a) b
    rwa [hRR] at h
  let T : Submodule ℂ F :=
    { carrier := {x | ∀ l : F →ₗ[ℂ] ℂ, (fun k => l (R k x)) ∈ W}
      add_mem' := fun {a b} ha hb l => by
        have h := W.add_mem (ha l) (hb l)
        convert h using 1
        ext k; simp
      zero_mem' := fun l => by
        have h := W.zero_mem
        convert h using 1
        ext k; simp
      smul_mem' := fun c x hx l => by
        have h := W.smul_mem c (hx l)
        convert h using 1
        ext k; simp }
  have hTR : ∀ g, ∀ x ∈ T, R g x ∈ T := fun g x hx l => by
    have h := hW _ (hx l) g
    convert h using 1
    ext k; simp [map_mul, Module.End.mul_apply]
  haveI : FiniteDimensional ℂ Y := hY
  haveI : FiniteDimensional ℂ (V ⊓ T : Submodule ℂ F) :=
    Submodule.finiteDimensional_of_le (S₂ := Y) fun x hx => hYV x hx.1 hx.2
  obtain ⟨P, hPm, hPo⟩ := exists_projL B hsym hpos (V ⊓ T)
  refine ⟨P z, (hPm z).1, hYV _ (hPm z).1 (hPm z).2, ?_⟩
  have hz1T : z - P z ∈ T := T.sub_mem hzt (hPm z).2
  have hZT : Submodule.span ℂ (Set.range fun k => R k (z - P z)) ≤ T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact hTR k _ hz1T
  have hZperp : ∀ a ∈ V ⊓ T, ∀ w ∈ Submodule.span ℂ (Set.range fun k => R k (z - P z)), B a w = 0 := by
    intro a ha w hw
    induction hw using Submodule.span_induction with
    | mem w h =>
      obtain ⟨k, rfl⟩ := h
      show B a (R k (z - P z)) = 0
      rw [hadj]
      exact hPo z _ ⟨hV _ _ ha.1, hTR _ _ ha.2⟩
    | zero => simp
    | add a' b _ _ ha' hb => rw [map_add, ha', hb, add_zero]
    | smul c a' _ ha' => rw [map_smul, ha', smul_zero]
  intro v hv
  haveI := hVf v hv
  obtain ⟨Q, hQm, hQo⟩ := exists_projL B hsym hpos (Submodule.span ℂ (Set.range fun k => R k v))
  have hV0V : Submodule.span ℂ (Set.range fun k => R k v) ≤ V := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact hV k v hv
  have hzero : ∀ d, B d d = 0 → d = 0 := fun d h => by
    by_contra h0
    have h1 := hpos d h0
    simp [h] at h1
  have hQR : ∀ g x, Q (R g x) = R g (Q x) := fun g x => by
    have hd : Q (R g x) - R g (Q x) ∈ Submodule.span ℂ (Set.range fun k => R k v) :=
      Submodule.sub_mem _ (hQm _) (orbit_stable R v g _ (hQm x))
    have h1 := hQo (R g x) _ hd
    have h2 : B (Q (R g x) - R g (Q x)) (R g x - R g (Q x)) = 0 := by
      rw [← map_sub, hadj]
      exact hQo x _ (orbit_stable R v g⁻¹ _ hd)
    have h3 : B (Q (R g x) - R g (Q x)) (Q (R g x) - R g (Q x)) = 0 := by
      have h4 : B (Q (R g x) - R g (Q x)) (Q (R g x) - R g (Q x)) =
          B (Q (R g x) - R g (Q x)) (R g x - R g (Q x)) -
            B (Q (R g x) - R g (Q x)) (R g x - Q (R g x)) := by
        rw [← map_sub]
        congr 1
        abel
      rw [h4, h1, h2, sub_zero]
    exact sub_eq_zero.1 (hzero _ h3)
  have hQT : ∀ w ∈ Submodule.span ℂ (Set.range fun k => R k (z - P z)), Q w ∈ T := fun w hw l => by
    have h := hZT hw (l ∘ₗ Q)
    convert h using 1
    ext k; simp [hQR]
  have hQ0 : Q (z - P z) = 0 := by
    have hw := self_mem_orbit R (z - P z)
    have h1 := hZperp (Q (z - P z)) ⟨hV0V (hQm _), hQT _ hw⟩ _ hw
    have h2 := hQo (z - P z) _ (hQm (z - P z))
    rw [map_sub, h1, zero_sub, neg_eq_zero] at h2
    exact hzero _ h2
  have h := hQo (z - P z) v (self_mem_orbit R v)
  rwa [hQ0, sub_zero] at h
