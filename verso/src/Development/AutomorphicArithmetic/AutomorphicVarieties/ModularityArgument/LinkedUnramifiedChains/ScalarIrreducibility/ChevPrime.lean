import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.ExtIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.ExistsBetweenFinset
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MinHom

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

/- English proof (translation)
Use `set p := P.comap (algebraMap B A)`. Use `haveI : Algebra.FiniteType B (A ⧸ P) := Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ B P) (Ideal.Quotient.mkₐ_surjective B P)`. Use `haveI : Algebra.FiniteType (B ⧸ p) (A ⧸ P) := Algebra.FiniteType.of_restrictScalars_finiteType B (B ⧸ p) (A ⧸ P)`. Take `⟨b', hb'0, hb'⟩` from `UpperTheory.V.J.chev (B ⧸ p) (A ⧸ P) Ideal.algebraMap_quotient_injective (Ideal.Quotient.mk P a) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b'`.

Use `⟨b, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hb'0` using `[Ne, Ideal.Quotient.eq_zero_iff_mem]`. Then use the resulting hypothesis. Introduce `K _ _ y hy hyb`. Set `y' : B ⧸ p →+* K` to `Ideal.Quotient.lift p y (fun x hx => (RingHom.mem_ker).mp (hy hx))`. Take `⟨ξ', hξ'1, hξ'2⟩` from `hb' K y' (by simpa [y'] using hyb)`.

Use `⟨ξ'.comp (Ideal.Quotient.mk P), ?_, hξ'2, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Establish `h` using `congrArg (fun f => f (Ideal.Quotient.mk p x)) hξ'1`. Simplify using `only [RingHom.comp_apply, y', Ideal.Quotient.lift_mk] at h ⊢`. Conclude with `h`.

Introduce `x hx`. Rewrite using `[RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]`.
-/
private theorem chev_prime (B A : Type) [CommRing B] [CommRing A] [Algebra B A] [Algebra.FiniteType B A]
    (P : Ideal A) [P.IsPrime] (a : A) (ha : a ∉ P) :
    ∃ b : B, b ∉ P.comap (algebraMap B A) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K),
      P.comap (algebraMap B A) ≤ RingHom.ker y → y b ≠ 0 →
        ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 ∧ P ≤ RingHom.ker ξ := by
  set p := P.comap (algebraMap B A)
  haveI : Algebra.FiniteType B (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ B P) (Ideal.Quotient.mkₐ_surjective B P)
  haveI : Algebra.FiniteType (B ⧸ p) (A ⧸ P) :=
    Algebra.FiniteType.of_restrictScalars_finiteType B (B ⧸ p) (A ⧸ P)
  obtain ⟨b', hb'0, hb'⟩ := UpperTheory.V.J.chev (B ⧸ p) (A ⧸ P) Ideal.algebraMap_quotient_injective
    (Ideal.Quotient.mk P a) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
  refine ⟨b, ?_, ?_⟩
  · rwa [Ne, Ideal.Quotient.eq_zero_iff_mem] at hb'0
  · intro K _ _ y hy hyb
    let y' : B ⧸ p →+* K := Ideal.Quotient.lift p y (fun x hx => (RingHom.mem_ker).mp (hy hx))
    obtain ⟨ξ', hξ'1, hξ'2⟩ := hb' K y' (by simpa [y'] using hyb)
    refine ⟨ξ'.comp (Ideal.Quotient.mk P), ?_, hξ'2, ?_⟩
    · ext x
      have h := congrArg (fun f => f (Ideal.Quotient.mk p x)) hξ'1
      simp only [RingHom.comp_apply, y', Ideal.Quotient.lift_mk] at h ⊢
      exact h
    · intro x hx
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `h (Ideal.span_le.2 hc)`.
-/
private theorem gen_out {R : Type} [CommRing R] {s : Set R} {P : Ideal R} (h : ¬ Ideal.span s ≤ P) :
    ∃ x ∈ s, x ∉ P := by
  by_contra hc
  push_neg at hc
  exact h (Ideal.span_le.2 hc)

/- English proof (translation)
Introduce `l _ c _ F C₀ n hF hn S P Gd hP hTI hext`. Take `⟨-, -, hgr0, -, hFT, -, hr⟩` from `Fr.gr_A hF hn S`. Use `haveI := hFT`. Use `haveI hPp : P.IsPrime := hP.1.1`. Establish `hTI' : (¬ S.u.triP ≤ P ∧ ¬ S.u.triM ≤ P) ∧ (n = 3 → ¬ S.u.ee ≤ P)` using `hTI`.

Take `⟨x1, ⟨g1, i1, j1, hlt1, rfl⟩, hx1⟩` from `gen_out (s := {x | ∃ g i, ∃ j < i, x = S.u.r g i j}) hTI'.1.1`. Take `⟨x2, ⟨g2, i2, j2, hlt2, rfl⟩, hx2⟩` from `gen_out (s := {x | ∃ g i j, i < j ∧ x = S.u.r g i j}) hTI'.1.2`. Choose the witnesses or unpack the hypotheses as in `⟨x3, ⟨k3, hx3k⟩, hx3P, hx3ee⟩ : ∃ x3 : S.A, (∃ k, x3 ∈ S.gr k) ∧ x3 ∉ P ∧ (n = 3 → x3 ∈ S.u.ee) := by`. Distinguish the cases in `h3 : n = 3`. Take `⟨x, ⟨g, i, j, hodd, rfl⟩, hx⟩` from `gen_out (s := {x | ∃ g i j, Odd (Fr.w n i - Fr.w n j) ∧ x = S.u.r g i j}) (hTI'.2 h3)`.

Conclude with `⟨_, ⟨_, hr g i j⟩, hx, fun _ => Ideal.subset_span ⟨g, i, j, hodd, rfl⟩⟩`. Use `⟨1, ⟨0, ?_⟩, (Ideal.ne_top_iff_one P).mp hPp.ne_top, fun h => absurd h h3⟩` and prove the remaining obligations. Rewrite using `[hgr0]`. Conclude with `Submodule.mem_one.mpr ⟨1, map_one _⟩`. Establish `ha : S.u.r g1 i1 j1 * S.u.r g2 i2 j2 * x3 ∉ P`.

Introduce `h`. Break down `hPp.mem_or_mem h with h | h` into its components or cases. Break down `hPp.mem_or_mem h with h | h` into its components or cases. Conclude with `hx1 h`. Conclude with `hx2 h`.

Conclude with `hx3P h`. Take `⟨b, hbP, hb⟩` from `chev_prime S.B S.A P _ ha`. Take `⟨y, hyP, hGd, hyb⟩` from `hext b hbP`. Take `⟨ξ0, hξ0, hξ0a, hPξ0⟩` from `hb (Qbar l) (y : S.B →+* Qbar l) (fun x hx => hyP hx) hyb`. Establish `hξ0' : ∀ x : S.B, ξ0 (S.inc x) = y x` using `fun x => congrArg (fun f : S.B →+* Qbar l => f x) hξ0`.

Set `ξ1 : S.A →ₐ[c.O] Qbar l` to `{ ξ0 with commutes' := fun r => by show ξ0 (algebraMap c.O S.A r) = algebraMap c.O (Qbar l) r`. Rewrite using `[← S.inc.commutes r, hξ0', y.commutes r] }`. Establish `hcomp : ξ1.comp S.inc = y`. Use extensionality with `x`. Conclude with `hξ0' x`.

Rewrite `hξ0a` using `[map_mul, map_mul, mul_ne_zero_iff, mul_ne_zero_iff]`. Take `⟨⟨h1, h2⟩, h3⟩` from `hξ0a`. Establish `hoff : S.u.OffTri (RingHom.ker ξ1)` using `⟨fun h => h1 (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g1, i1, j1, hlt1, rfl⟩))), fun h => h2 (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g2, i2, j2, hlt2, rfl⟩)))⟩`. Take `⟨ξ', hV, hc', hz⟩` from `UpperTheory.V.J.scale l c F C₀ n hF hn S ξ1 hoff`. Establish `hTIξ : S.u.TI (RingHom.ker ξ')` using `⟨⟨fun h => h1 ((hz _ _ (hr g1 i1 j1)).mp (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g1, i1, j1, hlt1, rfl⟩)))), fun h => h2 ((hz _ _ (hr g2 i2 j2)).mp (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g2, i2, j2, hlt2, rfl⟩))))⟩, fun hn3 h => h3 ((hz _ _ hx3k).mp (RingHom.mem_ker.mp (h …`.

Use `⟨ξ', hV, hTIξ, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hh` using `Fr.min_hom hF hn S P hP`. Unfold `Fr.Space.IsHom at hh`. Rewrite `hx` using `[hh]`.

Use `(Ideal.span_le.mpr ?_) hx` and prove the remaining obligations. Introduce and unpack `z ⟨hzP, k, hzk⟩`. Conclude with `RingHom.mem_ker.mpr ((hz k z hzk).mpr (RingHom.mem_ker.mp (hPξ0 hzP)))`. Rewrite using `[hc', hcomp]`. Conclude with `hGd`.
-/
theorem UpperTheory.V.J.genPt :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ (P : Ideal S.A) (Gd : (S.B →ₐ[c.O] Qbar l) → Prop), P ∈ minimalPrimes S.A → S.u.TI P →
          (∀ b ∉ S.π P, ∃ y : S.B →ₐ[c.O] Qbar l, S.π P ≤ RingHom.ker y ∧ Gd y ∧ y b ≠ 0) →
          ∃ ξ : S.A →ₐ[c.O] Qbar l, VPt S ξ ∧ S.u.TI (RingHom.ker ξ) ∧ P ≤ RingHom.ker ξ ∧ Gd (ξ.comp S.inc) := by
  intro l _ c _ F C₀ n hF hn S P Gd hP hTI hext
  obtain ⟨-, -, hgr0, -, hFT, -, hr⟩ := Fr.gr_A hF hn S
  haveI := hFT
  haveI hPp : P.IsPrime := hP.1.1
  have hTI' : (¬ S.u.triP ≤ P ∧ ¬ S.u.triM ≤ P) ∧ (n = 3 → ¬ S.u.ee ≤ P) := hTI
  obtain ⟨x1, ⟨g1, i1, j1, hlt1, rfl⟩, hx1⟩ :=
    gen_out (s := {x | ∃ g i, ∃ j < i, x = S.u.r g i j}) hTI'.1.1
  obtain ⟨x2, ⟨g2, i2, j2, hlt2, rfl⟩, hx2⟩ :=
    gen_out (s := {x | ∃ g i j, i < j ∧ x = S.u.r g i j}) hTI'.1.2
  obtain ⟨x3, ⟨k3, hx3k⟩, hx3P, hx3ee⟩ :
      ∃ x3 : S.A, (∃ k, x3 ∈ S.gr k) ∧ x3 ∉ P ∧ (n = 3 → x3 ∈ S.u.ee) := by
    by_cases h3 : n = 3
    · obtain ⟨x, ⟨g, i, j, hodd, rfl⟩, hx⟩ :=
        gen_out (s := {x | ∃ g i j, Odd (Fr.w n i - Fr.w n j) ∧ x = S.u.r g i j}) (hTI'.2 h3)
      exact ⟨_, ⟨_, hr g i j⟩, hx, fun _ => Ideal.subset_span ⟨g, i, j, hodd, rfl⟩⟩
    · refine ⟨1, ⟨0, ?_⟩, (Ideal.ne_top_iff_one P).mp hPp.ne_top, fun h => absurd h h3⟩
      rw [hgr0]
      exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have ha : S.u.r g1 i1 j1 * S.u.r g2 i2 j2 * x3 ∉ P := by
    intro h
    rcases hPp.mem_or_mem h with h | h
    · rcases hPp.mem_or_mem h with h | h
      · exact hx1 h
      · exact hx2 h
    · exact hx3P h
  obtain ⟨b, hbP, hb⟩ := chev_prime S.B S.A P _ ha
  obtain ⟨y, hyP, hGd, hyb⟩ := hext b hbP
  obtain ⟨ξ0, hξ0, hξ0a, hPξ0⟩ := hb (Qbar l) (y : S.B →+* Qbar l) (fun x hx => hyP hx) hyb
  have hξ0' : ∀ x : S.B, ξ0 (S.inc x) = y x := fun x =>
    congrArg (fun f : S.B →+* Qbar l => f x) hξ0
  let ξ1 : S.A →ₐ[c.O] Qbar l :=
    { ξ0 with
      commutes' := fun r => by
        show ξ0 (algebraMap c.O S.A r) = algebraMap c.O (Qbar l) r
        rw [← S.inc.commutes r, hξ0', y.commutes r] }
  have hcomp : ξ1.comp S.inc = y := by
    ext x
    exact hξ0' x
  rw [map_mul, map_mul, mul_ne_zero_iff, mul_ne_zero_iff] at hξ0a
  obtain ⟨⟨h1, h2⟩, h3⟩ := hξ0a
  have hoff : S.u.OffTri (RingHom.ker ξ1) :=
    ⟨fun h => h1 (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g1, i1, j1, hlt1, rfl⟩))),
      fun h => h2 (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g2, i2, j2, hlt2, rfl⟩)))⟩
  obtain ⟨ξ', hV, hc', hz⟩ := UpperTheory.V.J.scale l c F C₀ n hF hn S ξ1 hoff
  have hTIξ : S.u.TI (RingHom.ker ξ') :=
    ⟨⟨fun h => h1 ((hz _ _ (hr g1 i1 j1)).mp
        (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g1, i1, j1, hlt1, rfl⟩)))),
      fun h => h2 ((hz _ _ (hr g2 i2 j2)).mp
        (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g2, i2, j2, hlt2, rfl⟩))))⟩,
      fun hn3 h => h3 ((hz _ _ hx3k).mp (RingHom.mem_ker.mp (h (hx3ee hn3))))⟩
  refine ⟨ξ', hV, hTIξ, ?_, ?_⟩
  · intro x hx
    have hh := Fr.min_hom hF hn S P hP
    unfold Fr.Space.IsHom at hh
    rw [hh] at hx
    refine (Ideal.span_le.mpr ?_) hx
    rintro z ⟨hzP, k, hzk⟩
    exact RingHom.mem_ker.mpr ((hz k z hzk).mpr (RingHom.mem_ker.mp (hPξ0 hzP)))
  · rw [hc', hcomp]
    exact hGd
