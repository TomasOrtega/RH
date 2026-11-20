import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.LocalDualBase

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ w n J L p hJ hp hL _`. Substitute `hJ` using the available equality. Establish `hform1 : ∀ x y : Fin n → E, hform (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i`. Introduce `x y`. Unfold `hform`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[Matrix.one_apply]`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Use `⟨0, fun t => ⟨0, ?_⟩⟩` and prove the remaining obligations. Establish `: (t - (0 : intV E w) • (0 : latS (F` using `F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin 0) (Fin 0) E) L)))).1 = 0 := Subsingleton.elim _ _`.

Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Use `set R := w.adicCompletion F`. Set `l : Fin n` to `⟨n - 1, by omega⟩`. Establish `hl : l.1 + 1 = n` using `by simp [l]; omega`.

Establish `hσO : ∀ r : 𝓞 E, σ (r : E) ∈ (algebraMap (𝓞 E) E).range` using `fun r => ⟨⟨σ (r : E), map_isIntegral_int σ (RingOfIntegers.isIntegral_coe r)⟩, rfl⟩`. Take `⟨pb, hpb⟩` from `hσO p`. Establish `hpb0 : (algebraMap (𝓞 E) E pb) ≠ 0`. Rewrite using `[hpb]`. Introduce `h`.

Conclude with `hp (by simpa using (map_eq_zero σ).1 h)`. Use `set e0 : Fin n → E := Pi.single l (algebraMap (𝓞 E) E pb)⁻¹ with he0def`. Establish `he0 : e0 ∈ dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) L`. Introduce `x hx`. Rewrite using `[hform1, Finset.sum_eq_single l (by intro b _ hb; simp [e0, hb]) (by simp)]`.

Take `⟨r, hr, hd⟩` from `(hL x).1 hx l`. Take `⟨s, rfl⟩` from `hd hl`. Take `⟨u, hu⟩` from `hσO s`. Use `⟨u, ?_⟩` and prove the remaining obligations. Rewrite using `[hu, hr]`.

Simplify using `only [e0, Pi.single_eq_same]`. Use `push_cast`. Rewrite using `[map_mul, ← hpb]`. Clear the denominators using the available nonvanishing facts. Establish `hglob : ∀ y ∈ Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) L), ∃ r : 𝓞 E, y - (algebraMap (𝓞 E) E r) • e0 ∈ L`.

Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Establish `hxl : Pi.single l (p : E) ∈ L`. Use `(hL _).2 fun i => ?_` and prove the remaining obligations.

Distinguish the cases in `h : i = l`. Substitute `h` using the available equality. Conclude with `⟨p, by simp, fun _ => dvd_rfl⟩`. Conclude with `⟨0, by simp [h], fun _ => dvd_zero _⟩`. Establish `h1` using `hy _ hxl`.

Rewrite `h1` using `[hform1, Finset.sum_eq_single l (by intro b _ hb; simp [hb]) (by simp)]`. Simplify using `only [Pi.single_eq_same] at h1`. Take `⟨r, hr⟩` from `h1`. Use `⟨r, (hL _).2 fun j => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hj : j = l`.

Substitute `hj` using the available equality. Use `⟨0, ?_, fun _ => dvd_zero _⟩` and prove the remaining obligations. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e0, Pi.single_eq_same, hr, ← hpb]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hxj : Pi.single j (1 : E) ∈ L`. Use `(hL _).2 fun i => ?_` and prove the remaining obligations. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Conclude with `⟨1, by simp, fun hi => absurd (Fin.ext (by omega)) hj⟩`. Conclude with `⟨0, by simp [h], fun _ => dvd_zero _⟩`. Establish `h2` using `hy _ hxj`. Rewrite `h2` using `[hform1, Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)]`. Simplify using `only [Pi.single_eq_same, map_one, one_mul] at h2`.

Take `⟨u, hu⟩` from `h2`. Use `⟨u, ?_, fun hj' => absurd (Fin.ext (by omega)) hj⟩` and prove the remaining obligations. Simplify using `[e0, hj, hu]`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add y z _ _ h1 h2`.

Take `⟨r1, hr1⟩` from `h1`. Take `⟨r2, hr2⟩` from `h2`. Use `⟨r1 + r2, ?_⟩` and prove the remaining obligations. Establish `: y + z - (algebraMap (𝓞 E) E (r1 + r2)) • e0 = (y - (algebraMap (𝓞 E) E r1) • e0) + (z - (algebraMap (𝓞 E) E r2) • e0)`. Rewrite using `[map_add, add_smul]`.

Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Conclude with `L.add_mem hr1 hr2`. Consider the case `smul c y _ h`. Take `⟨r, hr⟩` from `h`.

Use `⟨c * r, ?_⟩` and prove the remaining obligations. Establish `: c • y - (algebraMap (𝓞 E) E (c * r)) • e0 = c • (y - (algebraMap (𝓞 E) E r) • e0)`. Use extensionality with `j`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_mul]`. Simplify using `only [Algebra.smul_def]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `L.smul_mem c hr`. Establish `hincl : ∀ r : 𝓞 E, inclE (F` using `F) R (algebraMap (𝓞 E) E r) ∈ intV E w := by`. Introduce `r`.

Conclude with `Subring.subset_closure (Or.inl ⟨⟨_, r, rfl⟩, rfl⟩)`. Use `⟨⟨fun i => inclE (F := F) R (e0 i), Submodule.subset_span ⟨e0, Submodule.subset_span he0, rfl⟩⟩, fun t => ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `t`. It suffices to establish `H : ∃ s : intV E w, t - (s : E ⊗[F] R) • (fun i => inclE (F` using `F) R (e0 i)) ∈ latS (F := F) R (intV E w) L by`. Take `⟨s, hs⟩` from `H`.

Conclude with `⟨s, hs⟩`. Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨y', hy', rfl⟩` from `hy`. Take `⟨r, hr⟩` from `hglob y' hy'`.

Use `⟨⟨_, hincl r⟩, ?_⟩` and prove the remaining obligations. Establish `: (fun i => inclE (F` using `F) R (y' i)) - inclE (F := F) R (algebraMap (𝓞 E) E r) • (fun i => inclE (F := F) R (e0 i)) = fun i => inclE (F := F) R ((y' - (algebraMap (𝓞 E) E r) • e0) i) := by`. Use extensionality with `i`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul]`. Rewrite using `[this]`.

Conclude with `Submodule.subset_span ⟨_, hr, rfl⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ h1 h2`. Take `⟨s1, hs1⟩` from `h1`. Take `⟨s2, hs2⟩` from `h2`.

Use `⟨s1 + s2, ?_⟩` and prove the remaining obligations. Establish `: x + y - ((s1 + s2 : intV E w) : E ⊗[F] R) • (fun i => inclE (F` using `F) R (e0 i)) = (x - (s1 : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i))) + (y - (s2 : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i))) := by`. Rewrite using `[Subring.coe_add, add_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`.

Conclude with `Submodule.add_mem _ hs1 hs2`. Consider the case `smul a x _ h`. Take `⟨s, hs⟩` from `h`. Use `⟨a * s, ?_⟩` and prove the remaining obligations. Establish `: a • x - ((a * s : intV E w) : E ⊗[F] R) • (fun i => inclE (F` using `F) R (e0 i)) = a • (x - (s : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i))) := by`.

Rewrite using `[Subring.coe_mul, mul_smul, smul_sub]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ a hs`.
-/
theorem localDual_eq_add_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (p : 𝓞 E), J = 1 → p ≠ 0 → (∀ x, x ∈ L ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → p ∣ r)) → (∀ x, σ (σ x) = x) → ∃ e : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∀ t : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J L)), ∃ s : intV E w, (t - s • e).1 ∈ latS (F := F) (w.adicCompletion F) (intV E w) L := by
  intro F E _ _ _ _ _ σ w n J L p hJ hp hL _
  subst hJ
  have hform1 : ∀ x y : Fin n → E, hform (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
    intro x y
    unfold hform
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Matrix.one_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, fun t => ⟨0, ?_⟩⟩
    have : (t - (0 : intV E w) • (0 : latS (F := F) (w.adicCompletion F) (intV E w)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin 0) (Fin 0) E) L)))).1 = 0 :=
      Subsingleton.elim _ _
    rw [this]
    exact Submodule.zero_mem _

  set R := w.adicCompletion F
  let l : Fin n := ⟨n - 1, by omega⟩
  have hl : l.1 + 1 = n := by simp [l]; omega
  have hσO : ∀ r : 𝓞 E, σ (r : E) ∈ (algebraMap (𝓞 E) E).range := fun r =>
    ⟨⟨σ (r : E), map_isIntegral_int σ (RingOfIntegers.isIntegral_coe r)⟩, rfl⟩
  obtain ⟨pb, hpb⟩ := hσO p
  have hpb0 : (algebraMap (𝓞 E) E pb) ≠ 0 := by
    rw [hpb]
    intro h
    exact hp (by simpa using (map_eq_zero σ).1 h)
  set e0 : Fin n → E := Pi.single l (algebraMap (𝓞 E) E pb)⁻¹ with he0def
  have he0 : e0 ∈ dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) L := by
    intro x hx
    rw [hform1, Finset.sum_eq_single l (by intro b _ hb; simp [e0, hb]) (by simp)]
    obtain ⟨r, hr, hd⟩ := (hL x).1 hx l
    obtain ⟨s, rfl⟩ := hd hl
    obtain ⟨u, hu⟩ := hσO s
    refine ⟨u, ?_⟩
    rw [hu, hr]
    simp only [e0, Pi.single_eq_same]
    push_cast
    rw [map_mul, ← hpb]
    field_simp
  have hglob : ∀ y ∈ Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) L),
      ∃ r : 𝓞 E, y - (algebraMap (𝓞 E) E r) • e0 ∈ L := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      have hxl : Pi.single l (p : E) ∈ L := by
        refine (hL _).2 fun i => ?_
        by_cases h : i = l
        · subst h
          exact ⟨p, by simp, fun _ => dvd_rfl⟩
        · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
      have h1 := hy _ hxl
      rw [hform1, Finset.sum_eq_single l (by intro b _ hb; simp [hb]) (by simp)] at h1
      simp only [Pi.single_eq_same] at h1
      obtain ⟨r, hr⟩ := h1
      refine ⟨r, (hL _).2 fun j => ?_⟩
      by_cases hj : j = l
      · subst hj
        refine ⟨0, ?_, fun _ => dvd_zero _⟩
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e0, Pi.single_eq_same, hr, ← hpb]
        push_cast
        field_simp
        ring
      · have hxj : Pi.single j (1 : E) ∈ L := by
          refine (hL _).2 fun i => ?_
          by_cases h : i = j
          · subst h
            exact ⟨1, by simp, fun hi => absurd (Fin.ext (by omega)) hj⟩
          · exact ⟨0, by simp [h], fun _ => dvd_zero _⟩
        have h2 := hy _ hxj
        rw [hform1, Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)] at h2
        simp only [Pi.single_eq_same, map_one, one_mul] at h2
        obtain ⟨u, hu⟩ := h2
        refine ⟨u, ?_, fun hj' => absurd (Fin.ext (by omega)) hj⟩
        simp [e0, hj, hu]
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ h1 h2 =>
      obtain ⟨r1, hr1⟩ := h1
      obtain ⟨r2, hr2⟩ := h2
      refine ⟨r1 + r2, ?_⟩
      have : y + z - (algebraMap (𝓞 E) E (r1 + r2)) • e0 =
          (y - (algebraMap (𝓞 E) E r1) • e0) + (z - (algebraMap (𝓞 E) E r2) • e0) := by
        rw [map_add, add_smul]; abel
      rw [this]
      exact L.add_mem hr1 hr2
    | smul c y _ h =>
      obtain ⟨r, hr⟩ := h
      refine ⟨c * r, ?_⟩
      have : c • y - (algebraMap (𝓞 E) E (c * r)) • e0 = c • (y - (algebraMap (𝓞 E) E r) • e0) := by
        ext j
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_mul]
        simp only [Algebra.smul_def]
        ring
      rw [this]
      exact L.smul_mem c hr
  have hincl : ∀ r : 𝓞 E, inclE (F := F) R (algebraMap (𝓞 E) E r) ∈ intV E w := by
    intro r
    exact Subring.subset_closure (Or.inl ⟨⟨_, r, rfl⟩, rfl⟩)
  refine ⟨⟨fun i => inclE (F := F) R (e0 i),
    Submodule.subset_span ⟨e0, Submodule.subset_span he0, rfl⟩⟩, fun t => ?_⟩
  obtain ⟨t, ht⟩ := t
  suffices H : ∃ s : intV E w, t - (s : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i)) ∈
      latS (F := F) R (intV E w) L by
    obtain ⟨s, hs⟩ := H
    exact ⟨s, hs⟩
  induction ht using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨r, hr⟩ := hglob y' hy'
    refine ⟨⟨_, hincl r⟩, ?_⟩
    have : (fun i => inclE (F := F) R (y' i)) - inclE (F := F) R (algebraMap (𝓞 E) E r) •
        (fun i => inclE (F := F) R (e0 i)) =
        fun i => inclE (F := F) R ((y' - (algebraMap (𝓞 E) E r) • e0) i) := by
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul]
    rw [this]
    exact Submodule.subset_span ⟨_, hr, rfl⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨s1, hs1⟩ := h1
    obtain ⟨s2, hs2⟩ := h2
    refine ⟨s1 + s2, ?_⟩
    have : x + y - ((s1 + s2 : intV E w) : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i)) =
        (x - (s1 : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i))) +
        (y - (s2 : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i))) := by
      rw [Subring.coe_add, add_smul]; abel
    rw [this]
    exact Submodule.add_mem _ hs1 hs2
  | smul a x _ h =>
    obtain ⟨s, hs⟩ := h
    refine ⟨a * s, ?_⟩
    have : a • x - ((a * s : intV E w) : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i)) =
        a • (x - (s : E ⊗[F] R) • (fun i => inclE (F := F) R (e0 i))) := by
      rw [Subring.coe_mul, mul_smul, smul_sub]
      rfl
    rw [this]
    exact Submodule.smul_mem _ a hs

end GlobalTheory.Mem.LocalDualBase
