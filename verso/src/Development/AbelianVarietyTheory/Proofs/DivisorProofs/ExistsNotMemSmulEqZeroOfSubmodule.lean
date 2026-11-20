import Mathlib
open TensorProduct Polynomial

namespace GlobalTheory.NakAug

/- English proof (translation)
Introduce `hmem`. Rewrite `hmem` using `[eval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_mul]`. Establish `hs : ∑ i ∈ Finset.range p.natDegree, p.coeff i * t ^ i ∈ P`. Use `Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ ?_` and prove the remaining obligations. Establish `hi' : i < p.natDegree` using `Finset.mem_range.mp hi`.

Conclude with `Ideal.pow_le_self (by omega) (hc i)`. Establish `: t ^ p.natDegree ∈ P`. Use `P.sub_mem hmem hs` as an intermediate fact. Simplify using `using this`. Conclude with `ht (Ideal.IsPrime.mem_of_pow_mem inferInstance _ this)`.
-/
theorem eval_notMem_of_monic {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime] (p : A[X])
    (hmon : p.Monic) (hc : ∀ k, p.coeff k ∈ P ^ (p.natDegree - k)) (t : A) (ht : t ∉ P) :
    p.eval t ∉ P := by
  intro hmem
  rw [eval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_mul] at hmem
  have hs : ∑ i ∈ Finset.range p.natDegree, p.coeff i * t ^ i ∈ P := by
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ ?_
    have hi' : i < p.natDegree := Finset.mem_range.mp hi
    exact Ideal.pow_le_self (by omega) (hc i)
  have : t ^ p.natDegree ∈ P := by
    have := P.sub_mem hmem hs
    simpa using this
  exact ht (Ideal.IsPrime.mem_of_pow_mem inferInstance _ this)

/- English proof (translation)
Take `⟨p, hmon, -, hc, h0⟩` from `LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero A (algebraMap A (Module.End A M) t) P (by`. Introduce and unpack `_ ⟨m, rfl⟩`. Simplify `h m)` using `[Module.algebraMap_end_apply]`. Use `⟨p.eval t, eval_notMem_of_monic P p hmon hc t ht, fun m => ?_⟩` and prove the remaining obligations. Rewrite `h0` using `[aeval_algebraMap_apply_eq_algebraMap_eval]`.

Use `congrArg (fun φ : Module.End A M => φ m) h0` as an intermediate fact. Simplify `this` using `[Module.algebraMap_end_apply]`.
-/
theorem exists_notMem_smul_eq_zero {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (P : Ideal A) [P.IsPrime] (t : A) (ht : t ∉ P)
    (h : ∀ m : M, t • m ∈ P • (⊤ : Submodule A M)) :
    ∃ g : A, g ∉ P ∧ ∀ m : M, g • m = 0 := by
  obtain ⟨p, hmon, -, hc, h0⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero A
      (algebraMap A (Module.End A M) t) P (by
        rintro _ ⟨m, rfl⟩
        simpa [Module.algebraMap_end_apply] using h m)
  refine ⟨p.eval t, eval_notMem_of_monic P p hmon hc t ht, fun m => ?_⟩
  rw [aeval_algebraMap_apply_eq_algebraMap_eval] at h0
  have := congrArg (fun φ : Module.End A M => φ m) h0
  simpa [Module.algebraMap_end_apply] using this

/- English proof (translation)
Use `haveI : Module.Finite A N := Module.Finite.iff_fg.mpr hN`. Take `⟨g, hg, h0⟩` from `exists_notMem_smul_eq_zero (M := N) P t ht (fun m => by`. Establish `hm` using `h m m.2`. Establish `hmap : P • N = (P • (⊤ : Submodule A N)).map N.subtype`. Rewrite using `[Submodule.map_smul'', Submodule.map_subtype_top]`.

Rewrite `hm` using `[hmap]`. Take `⟨z, hz, hzm⟩` from `hm`. Establish `: z = t • m` using `Subtype.ext (by simpa using hzm)`. Conclude with `this ▸ hz)`. Conclude with `⟨g, hg, fun m hm => by simpa using congrArg Subtype.val (h0 ⟨m, hm⟩)⟩`.
-/
theorem exists_notMem_smul_eq_zero_of_submodule {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (P : Ideal A) [P.IsPrime] (N : Submodule A M) (hN : N.FG) (t : A) (ht : t ∉ P)
    (h : ∀ m ∈ N, t • m ∈ P • N) :
    ∃ g : A, g ∉ P ∧ ∀ m ∈ N, g • m = 0 := by
  haveI : Module.Finite A N := Module.Finite.iff_fg.mpr hN
  obtain ⟨g, hg, h0⟩ := exists_notMem_smul_eq_zero (M := N) P t ht (fun m => by
    have hm := h m m.2
    have hmap : P • N = (P • (⊤ : Submodule A N)).map N.subtype := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top]
    rw [hmap] at hm
    obtain ⟨z, hz, hzm⟩ := hm
    have : z = t • m := Subtype.ext (by simpa using hzm)
    exact this ▸ hz)
  exact ⟨g, hg, fun m hm => by simpa using congrArg Subtype.val (h0 ⟨m, hm⟩)⟩

/- English proof (translation)
Take `⟨s, hs⟩` from `(Module.Finite.fg_top : (⊤ : Submodule A M).FG)`. Establish `key : ∀ t : Finset M, ∃ f : A, f ∉ P ∧ ∀ b ∈ t, f • D b ∈ S`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => exact ⟨1, fun h1 => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h1), by simp⟩`.

Consider the case `insert a t ha ih`. Take `⟨F, hF, hFt⟩` from `ih`. Take `⟨fa, hfa, hfaa⟩` from `h a`. Use `⟨fa * F, fun hm => (hP.mem_or_mem hm).elim hfa hF, fun b hb => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.mp hb with rfl | hb` into its components or cases.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `S.smul_mem _ hfaa`. Rewrite using `[mul_smul]`. Conclude with `S.smul_mem _ (hFt b hb)`. Take `⟨f, hf, hfs⟩` from `key s`.

Use `⟨f, hf, fun b => ?_⟩` and prove the remaining obligations. Establish `hle : Submodule.span A (s : Set M) ≤ S.comap (f • D)`. Rewrite using `[Submodule.span_le]`. Introduce `b hb`. Conclude with `hfs b hb`.

Establish `hb : b ∈ Submodule.span A (s : Set M)` using `hs ▸ Submodule.mem_top`. Simplify using `using hle hb`.
-/
theorem exists_uniform_notMem {A M M' : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] [Module.Finite A M] (P : Ideal A) [hP : P.IsPrime]
    (S : Submodule A M') (D : M →ₗ[A] M') (h : ∀ b, ∃ f : A, f ∉ P ∧ f • D b ∈ S) :
    ∃ f : A, f ∉ P ∧ ∀ b, f • D b ∈ S := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule A M).FG)
  have key : ∀ t : Finset M, ∃ f : A, f ∉ P ∧ ∀ b ∈ t, f • D b ∈ S := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1, fun h1 => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h1), by simp⟩
    | insert a t ha ih =>
      obtain ⟨F, hF, hFt⟩ := ih
      obtain ⟨fa, hfa, hfaa⟩ := h a
      refine ⟨fa * F, fun hm => (hP.mem_or_mem hm).elim hfa hF, fun b hb => ?_⟩
      rcases Finset.mem_insert.mp hb with rfl | hb
      · rw [mul_comm, mul_smul]; exact S.smul_mem _ hfaa
      · rw [mul_smul]; exact S.smul_mem _ (hFt b hb)
  obtain ⟨f, hf, hfs⟩ := key s
  refine ⟨f, hf, fun b => ?_⟩
  have hle : Submodule.span A (s : Set M) ≤ S.comap (f • D) := by
    rw [Submodule.span_le]
    intro b hb
    exact hfs b hb
  have hb : b ∈ Submodule.span A (s : Set M) := hs ▸ Submodule.mem_top
  simpa using hle hb

/- English proof (translation)
Use `set J : Ideal B := RingHom.ker ε with hJdef`. Use `set Q : Ideal B := P.map (algebraMap A B) with hQdef`. Use `haveI : IsNoetherian A B := isNoetherian_of_isNoetherianRing_of_finite A B`. Set `D : B →ₗ[A] B` to `α.toLinearMap - (Algebra.linearMap A B).comp ε.toLinearMap`. Establish `hDapp : ∀ b, D b = α b - algebraMap A B (ε b)` using `fun b => rfl`.

Take `⟨f, hf, hfD⟩` from `exists_uniform_notMem P (Q.restrictScalars A) D (fun b => by simpa only [hDapp, Submodule.restrictScalars_mem] using h3 b)`. Establish `hmemJ : ∀ x, x ∈ J ↔ ε x = 0` using `fun x => RingHom.mem_ker`. Establish `hφ : ∀ b, b - algebraMap A B (ε b) ∈ J` using `fun b => by`. Rewrite using `[hmemJ, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]`. Establish `hαφ : ∀ b, α (b - algebraMap A B (ε b)) = α b - algebraMap A B (ε b)` using `fun b => by`.

Rewrite using `[map_sub, AlgHom.commutes]`. Establish `hαJ : ∀ x ∈ J, α x ∈ J` using `fun x hx => by`. Establish `h` using `h2 x hx`. Establish `e : α x = (α x - (d : B) * x) + (d : B) * x` using `by ring`. Rewrite using `[e]`.

Conclude with `J.add_mem (Ideal.pow_le_self two_ne_zero h) (J.mul_mem_left _ hx)`. Establish `hfαQ : ∀ x ∈ J, algebraMap A B f * α x ∈ Q` using `fun x hx => by`. Establish `h` using `hfD x`. Rewrite `h` using `[hDapp, (hmemJ x).mp hx, map_zero, sub_zero, Algebra.smul_def]`. Conclude with `h`.

Establish `hL1 : ∀ y ∈ Q, y ∈ J → y ∈ P • J.restrictScalars A` using `fun y hyQ hyJ => by`. Set `φ : B →ₗ[A] B` to `LinearMap.id - (Algebra.linearMap A B).comp ε.toLinearMap`. Establish `hy : y ∈ P • (⊤ : Submodule A B)`. Rewrite using `[Ideal.smul_top_eq_map]`. Conclude with `hyQ`.

Establish `h1 : φ y ∈ (P • (⊤ : Submodule A B)).map φ` using `Submodule.mem_map_of_mem hy`. Rewrite `h1` using `[Submodule.map_smul'']`. Establish `hle : (⊤ : Submodule A B).map φ ≤ J.restrictScalars A`. Introduce and unpack `_ ⟨b, -, rfl⟩`. Conclude with `hφ b`.

Establish `hφy : φ y = y` using `by show y - algebraMap A B (ε y) = y`. Rewrite using `[(hmemJ y).mp hyJ, map_zero, sub_zero]`. Rewrite `h1` using `[hφy]`. Conclude with `Submodule.smul_mono le_rfl hle h1`. Establish `hs : ∃ s : A, s ∉ P ∧ ∀ x ∈ J, algebraMap A B s * x ∈ J ^ 2`.

Set `L : B →ₗ[A] B ⧸ J ^ 2` to `(Ideal.Quotient.mkₐ A (J ^ 2)).toLinearMap`. Establish `hL : ∀ x, L x = Ideal.Quotient.mk (J ^ 2) x` using `fun x => rfl`. Set `N : Submodule A (B ⧸ J ^ 2)` to `(J.map (Ideal.Quotient.mk (J ^ 2))).restrictScalars A`. Establish `hNfg : N.FG` using `IsNoetherian.noetherian N`. Take `⟨s, hs, hs0⟩` from `exists_notMem_smul_eq_zero_of_submodule P N hNfg (f * d) (fun hm => (hP.mem_or_mem hm).elim hf hd) (fun m hm => by`.

Take `⟨x, hx, rfl⟩` from `(Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hm`. Establish `e1 : (f * (d : A)) • Ideal.Quotient.mk (J ^ 2) x = L (algebraMap A B f * α x)`. Rewrite using `[← hL, ← map_smul, hL, hL, Ideal.Quotient.eq, Algebra.smul_def, map_mul, map_natCast]`. Establish `: algebraMap A B f * (d : B) * x - algebraMap A B f * α x = - (algebraMap A B f * (α x - (d : B) * x))` using `by ring`. Rewrite using `[this]`.

Conclude with `(J ^ 2).neg_mem ((J ^ 2).mul_mem_left _ (h2 x hx))`. Rewrite using `[e1]`. Establish `hy` using `hL1 _ (hfαQ x hx) (J.mul_mem_left _ (hαJ x hx))`. Establish `h1 : L (algebraMap A B f * α x) ∈ (P • J.restrictScalars A).map L` using `Submodule.mem_map_of_mem hy`. Rewrite `h1` using `[Submodule.map_smul'']`.

Use `Submodule.smul_mono le_rfl ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `Ideal.mem_map_of_mem _ hz)`. Use `⟨s, hs, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h0` using `hs0 _ (Ideal.mem_map_of_mem (Ideal.Quotient.mk (J ^ 2)) hx)`.

Rewrite `h0` using `[← hL, ← map_smul, hL, Ideal.Quotient.eq_zero_iff_mem, Algebra.smul_def]`. Conclude with `h0`. Take `⟨s, hsP, hsJ⟩` from `hs`. Use `set K : Ideal B := J.map α with hKdef`. Establish `hKfg : (K.restrictScalars A).FG` using `IsNoetherian.noetherian _`.

Establish `hJ2 : ∀ y ∈ J ^ 2, algebraMap A B f * α y ∈ Q * K`. Introduce `y hy`. Rewrite `hy` using `[pow_two]`. Use `Submodule.mul_induction_on hy (fun y1 hy1 y2 hy2 => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, ← mul_assoc]`.

Conclude with `Ideal.mul_mem_mul (hfαQ y1 hy1) (Ideal.mem_map_of_mem α hy2)`. Rewrite using `[map_add, mul_add]`. Conclude with `Ideal.add_mem _ ha hb`. Establish `hKt : ∀ m ∈ K.restrictScalars A, (s * f) • m ∈ P • K.restrictScalars A`. Introduce `m hm`.

Rewrite using `[← Ideal.smul_restrictScalars, Submodule.restrictScalars_mem, Ideal.smul_eq_mul, Algebra.smul_def]`. Rewrite `hm` using `[Submodule.restrictScalars_mem]`. Use `Submodule.span_induction (p := fun m _ => algebraMap A B (s * f) * m ∈ Q * K) ?_ ?_ ?_ ?_ hm` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `e : algebraMap A B (s * f) * α x = algebraMap A B f * α (algebraMap A B s * x)`.

Rewrite using `[map_mul, map_mul, AlgHom.commutes]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `hJ2 _ (hsJ x hx)`. Simplify using the standard rewrite rules.

Introduce `x y _ _ hx hy`. Rewrite using `[mul_add]`. Conclude with `Ideal.add_mem _ hx hy`. Introduce `b x _ hx`. Rewrite using `[smul_eq_mul, mul_left_comm]`.

Conclude with `Ideal.mul_mem_left _ b hx`. Take `⟨g, hg, hg0⟩` from `exists_notMem_smul_eq_zero_of_submodule P (K.restrictScalars A) hKfg (s * f) (fun hm => (hP.mem_or_mem hm).elim hsP hf) hKt`. Use `⟨g, hg, fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[← hαφ]`. Conclude with `hg0 _ (Ideal.mem_map_of_mem α (hφ b))`.
-/
theorem augmentation_agrees_after_inverting
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A] [Module.Finite A B]
    (P : Ideal A) [hP : P.IsPrime] (ε : B →ₐ[A] A) (α : B →ₐ[A] B) (d : ℕ) (hd : (d : A) ∉ P)
    (h2 : ∀ x ∈ RingHom.ker ε, α x - (d : B) * x ∈ (RingHom.ker ε) ^ 2)
    (h3 : ∀ b, ∃ f : A, f ∉ P ∧ f • (α b - algebraMap A B (ε b)) ∈ P.map (algebraMap A B)) :
    ∃ g : A, g ∉ P ∧ ∀ b, g • (α b - algebraMap A B (ε b)) = 0 := by
  classical
  set J : Ideal B := RingHom.ker ε with hJdef
  set Q : Ideal B := P.map (algebraMap A B) with hQdef
  haveI : IsNoetherian A B := isNoetherian_of_isNoetherianRing_of_finite A B

  let D : B →ₗ[A] B := α.toLinearMap - (Algebra.linearMap A B).comp ε.toLinearMap
  have hDapp : ∀ b, D b = α b - algebraMap A B (ε b) := fun b => rfl
  obtain ⟨f, hf, hfD⟩ := exists_uniform_notMem P (Q.restrictScalars A) D
    (fun b => by simpa only [hDapp, Submodule.restrictScalars_mem] using h3 b)
  have hmemJ : ∀ x, x ∈ J ↔ ε x = 0 := fun x => RingHom.mem_ker
  have hφ : ∀ b, b - algebraMap A B (ε b) ∈ J := fun b => by
    rw [hmemJ, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hαφ : ∀ b, α (b - algebraMap A B (ε b)) = α b - algebraMap A B (ε b) := fun b => by
    rw [map_sub, AlgHom.commutes]
  have hαJ : ∀ x ∈ J, α x ∈ J := fun x hx => by
    have h := h2 x hx
    have e : α x = (α x - (d : B) * x) + (d : B) * x := by ring
    rw [e]
    exact J.add_mem (Ideal.pow_le_self two_ne_zero h) (J.mul_mem_left _ hx)

  have hfαQ : ∀ x ∈ J, algebraMap A B f * α x ∈ Q := fun x hx => by
    have h := hfD x
    rw [hDapp, (hmemJ x).mp hx, map_zero, sub_zero, Algebra.smul_def] at h
    exact h

  have hL1 : ∀ y ∈ Q, y ∈ J → y ∈ P • J.restrictScalars A := fun y hyQ hyJ => by
    let φ : B →ₗ[A] B := LinearMap.id - (Algebra.linearMap A B).comp ε.toLinearMap
    have hy : y ∈ P • (⊤ : Submodule A B) := by
      rw [Ideal.smul_top_eq_map]; exact hyQ
    have h1 : φ y ∈ (P • (⊤ : Submodule A B)).map φ := Submodule.mem_map_of_mem hy
    rw [Submodule.map_smul''] at h1
    have hle : (⊤ : Submodule A B).map φ ≤ J.restrictScalars A := by
      rintro _ ⟨b, -, rfl⟩
      exact hφ b
    have hφy : φ y = y := by
      show y - algebraMap A B (ε y) = y
      rw [(hmemJ y).mp hyJ, map_zero, sub_zero]
    rw [hφy] at h1
    exact Submodule.smul_mono le_rfl hle h1

  have hs : ∃ s : A, s ∉ P ∧ ∀ x ∈ J, algebraMap A B s * x ∈ J ^ 2 := by
    let L : B →ₗ[A] B ⧸ J ^ 2 := (Ideal.Quotient.mkₐ A (J ^ 2)).toLinearMap
    have hL : ∀ x, L x = Ideal.Quotient.mk (J ^ 2) x := fun x => rfl
    let N : Submodule A (B ⧸ J ^ 2) := (J.map (Ideal.Quotient.mk (J ^ 2))).restrictScalars A
    have hNfg : N.FG := IsNoetherian.noetherian N
    obtain ⟨s, hs, hs0⟩ := exists_notMem_smul_eq_zero_of_submodule P N hNfg (f * d)
      (fun hm => (hP.mem_or_mem hm).elim hf hd) (fun m hm => by
        obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hm
        have e1 : (f * (d : A)) • Ideal.Quotient.mk (J ^ 2) x
            = L (algebraMap A B f * α x) := by
          rw [← hL, ← map_smul, hL, hL, Ideal.Quotient.eq, Algebra.smul_def, map_mul, map_natCast]
          have : algebraMap A B f * (d : B) * x - algebraMap A B f * α x
              = - (algebraMap A B f * (α x - (d : B) * x)) := by ring
          rw [this]
          exact (J ^ 2).neg_mem ((J ^ 2).mul_mem_left _ (h2 x hx))
        rw [e1]
        have hy := hL1 _ (hfαQ x hx) (J.mul_mem_left _ (hαJ x hx))
        have h1 : L (algebraMap A B f * α x) ∈ (P • J.restrictScalars A).map L :=
          Submodule.mem_map_of_mem hy
        rw [Submodule.map_smul''] at h1
        refine Submodule.smul_mono le_rfl ?_ h1
        rintro _ ⟨z, hz, rfl⟩
        exact Ideal.mem_map_of_mem _ hz)
    refine ⟨s, hs, fun x hx => ?_⟩
    have h0 := hs0 _ (Ideal.mem_map_of_mem (Ideal.Quotient.mk (J ^ 2)) hx)
    rw [← hL, ← map_smul, hL, Ideal.Quotient.eq_zero_iff_mem, Algebra.smul_def] at h0
    exact h0
  obtain ⟨s, hsP, hsJ⟩ := hs

  set K : Ideal B := J.map α with hKdef
  have hKfg : (K.restrictScalars A).FG := IsNoetherian.noetherian _
  have hJ2 : ∀ y ∈ J ^ 2, algebraMap A B f * α y ∈ Q * K := by
    intro y hy
    rw [pow_two] at hy
    refine Submodule.mul_induction_on hy (fun y1 hy1 y2 hy2 => ?_) (fun a b ha hb => ?_)
    · rw [map_mul, ← mul_assoc]
      exact Ideal.mul_mem_mul (hfαQ y1 hy1) (Ideal.mem_map_of_mem α hy2)
    · rw [map_add, mul_add]; exact Ideal.add_mem _ ha hb
  have hKt : ∀ m ∈ K.restrictScalars A, (s * f) • m ∈ P • K.restrictScalars A := by
    intro m hm
    rw [← Ideal.smul_restrictScalars, Submodule.restrictScalars_mem, Ideal.smul_eq_mul,
      Algebra.smul_def]
    rw [Submodule.restrictScalars_mem] at hm
    refine Submodule.span_induction (p := fun m _ => algebraMap A B (s * f) * m ∈ Q * K)
      ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨x, hx, rfl⟩
      have e : algebraMap A B (s * f) * α x = algebraMap A B f * α (algebraMap A B s * x) := by
        rw [map_mul, map_mul, AlgHom.commutes]; ring
      rw [e]; exact hJ2 _ (hsJ x hx)
    · simp
    · intro x y _ _ hx hy; rw [mul_add]; exact Ideal.add_mem _ hx hy
    · intro b x _ hx; rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ b hx
  obtain ⟨g, hg, hg0⟩ := exists_notMem_smul_eq_zero_of_submodule P (K.restrictScalars A) hKfg
    (s * f) (fun hm => (hP.mem_or_mem hm).elim hsP hf) hKt
  refine ⟨g, hg, fun b => ?_⟩
  rw [← hαφ]
  exact hg0 _ (Ideal.mem_map_of_mem α (hφ b))

end GlobalTheory.NakAug
