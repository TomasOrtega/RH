import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotFiltSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PDomination
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace SnapperQuotFilt

section Twist

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

/- English proof (translation)
Use `SubSystem.ext_sub fun I => le_antisymm ?_ ?_` and prove the remaining obligations. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨q, hq, z, hz, rfl⟩`. Express the relevant statement in the definitionally equal form `z ∈ Submodule.span _ _ at hz`. Proceed by induction on `hz using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨p, hp, y, hy, rfl⟩` from `hz`. Use `Submodule.subset_span ⟨q * p, Submodule.subset_span ⟨q, hq, p, hp, rfl⟩, y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul]`. Consider the case `zero => rw [smul_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [smul_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul a z _ hz`. Express the relevant statement in the definitionally equal form `q • ((a : Ω) • z) ∈ _`.

Rewrite using `[smul_smul, mul_comm, ← smul_smul]`. Conclude with `Submodule.smul_mem _ a hz`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨r, hr, y, hy, rfl⟩`. Express the relevant statement in the definitionally equal form `r ∈ Submodule.span _ _ at hr`.

Proceed by induction on `hr using Submodule.span_induction with`. Consider the case `mem r hr`. Take `⟨q, hq, p, hp, rfl⟩` from `hr`. Use `Submodule.subset_span ⟨q, hq, p • y, Submodule.subset_span ⟨p, hp, y, hy, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, mul_smul]`.

Consider the case `zero => rw [zero_smul]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [add_smul]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul a r _ hr`.

Express the relevant statement in the definitionally equal form `((a : Ω) * r) • y ∈ _`. Rewrite using `[mul_smul]`. Conclude with `Submodule.smul_mem _ a hr`.
-/
theorem twist_twist (F : SubSystem S x E) (P Q : SubSystem S x Ω) :
    (F.twist P).twist Q = F.twist (P.twist Q) := by
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, z, hz, rfl⟩
    change z ∈ Submodule.span _ _ at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨p, hp, y, hy, rfl⟩ := hz
      refine Submodule.subset_span ⟨q * p, Submodule.subset_span ⟨q, hq, p, hp, rfl⟩, y, hy, ?_⟩
      rw [mul_smul]
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul a z _ hz =>
      change q • ((a : Ω) • z) ∈ _
      rw [smul_smul, mul_comm, ← smul_smul]
      exact Submodule.smul_mem _ a hz
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨r, hr, y, hy, rfl⟩
    change r ∈ Submodule.span _ _ at hr
    induction hr using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨q, hq, p, hp, rfl⟩ := hr
      refine Submodule.subset_span ⟨q, hq, p • y, Submodule.subset_span ⟨p, hp, y, hy, rfl⟩, ?_⟩
      rw [smul_eq_mul, mul_smul]
    | zero => rw [zero_smul]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [add_smul]; exact Submodule.add_mem _ ha hb
    | smul a r _ hr =>
      change ((a : Ω) * r) • y ∈ _
      rw [mul_smul]
      exact Submodule.smul_mem _ a hr

def powsBundle : (t : ℕ) → (Fin t → LineBundle S x) → (Fin t → ℕ) → LineBundle S x
  | 0, _, _ => twistBundle S x 0
  | t + 1, L, n => (powsBundle t (fun j => L j.castSucc) (fun j => n j.castSucc)).tensorProd
      ((L (Fin.last t)).powBundle (n (Fin.last t)))

/- English proof (translation)
The claim follows from `| 0, _, _ => by change F = F.twist (twistSys S x 0) rw [SubSystem.twist_twistSys_zero] | t + 1, L, n => by change (F.twistPows t (fun j => (L j.castSucc).toSubSystem) (fun j => n j.castSucc)).twist (((L (Fin.last t)).toSubSystem).pow (n (Fin.last t))) = _ rw [twistPows_eq F t, tw …`.
-/
theorem twistPows_eq (F : SubSystem S x E) : ∀ (t : ℕ) (L : Fin t → LineBundle S x) (n : Fin t → ℕ),
    F.twistPows t (fun j => (L j).toSubSystem) n = F.twist (powsBundle t L n).toSubSystem
  | 0, _, _ => by
    change F = F.twist (twistSys S x 0)
    rw [SubSystem.twist_twistSys_zero]
  | t + 1, L, n => by
    change (F.twistPows t (fun j => (L j.castSucc).toSubSystem) (fun j => n j.castSucc)).twist
      (((L (Fin.last t)).toSubSystem).pow (n (Fin.last t))) = _
    rw [twistPows_eq F t, twist_twist, ← LineBundle.powBundle_toSubSystem]
    rfl

end Twist

section Tilde

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

omit [IsScalarTower S Ω E] in

/- English proof (translation)
The claim follows from `Submodule.span_mono fun _ ⟨m, s, a, e, hs, hse, hm, hae, hy⟩ => ⟨m, s, a, e, hs, hse, h a hm, hae, hy⟩`.
-/
theorem tilde_mono {M M' : FinGradedSub (S := S) (x := x) E} (h : ∀ c, M.piece c ≤ M'.piece c) (c : ℤ)
    (I : Chart x) : M.tilde c I ≤ M'.tilde c I :=
  Submodule.span_mono fun _ ⟨m, s, a, e, hs, hse, hm, hae, hy⟩ => ⟨m, s, a, e, hs, hse, h a hm, hae, hy⟩

omit [IsScalarTower S Ω E] in

def tildeFam (M : FinGradedSub (S := S) (x := x) E) : SubFamily S x E where
  toSubSystem := M.tildeSys 0
  mem_iff I J h y := by
    constructor
    · intro hy
      change y ∈ M.tilde 0 J at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩ := hy
        obtain ⟨i, hi⟩ := I.2.1
        have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
        have hs0 := eval_ne_zero_of_mem_monos J hs
        have hX0 : aeval x (X i ^ e : Poly S N) ≠ 0 := by
          rw [map_pow, aeval_X]; exact pow_ne_zero _ hxi
        refine ⟨⟨aeval x s / aeval x (X i ^ e), s, X i ^ e, e, pow_mem (X_mem_monos hi) e, hse,
          isHomogeneous_X_pow i e, rfl⟩, ?_, ?_⟩
        · rw [isUnit_iff_exists_inv]
          refine ⟨⟨aeval x (X i ^ e) / aeval x s, X i ^ e, s, e, hs, isHomogeneous_X_pow i e, hse, rfl⟩, ?_⟩
          apply Subtype.ext
          change aeval x s / aeval x (X i ^ e) * (aeval x (X i ^ e) / aeval x s) = 1
          field_simp
        · change (aeval x s / aeval x (X i ^ e)) • ((aeval x s)⁻¹ • m) ∈ M.tilde 0 I
          rw [smul_smul, show aeval x s / aeval x (X i ^ e) * (aeval x s)⁻¹ = (aeval x (X i ^ e))⁻¹ by
            field_simp]
          exact Submodule.subset_span ⟨m, X i ^ e, a, e, pow_mem (X_mem_monos hi) e,
            isHomogeneous_X_pow i e, hm, hae, rfl⟩
      | zero => exact ⟨1, by simp, by rw [smul_zero]; exact Submodule.zero_mem _⟩
      | add y₁ y₂ _ _ h₁ h₂ =>
        obtain ⟨a₁, ha₁, h₁⟩ := h₁
        obtain ⟨a₂, ha₂, h₂⟩ := h₂
        refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
        have : ((a₁ * a₂ : chartRing S x I) : Ω) • (y₁ + y₂) =
            a₂ • ((a₁ : Ω) • y₁) + a₁ • ((a₂ : Ω) • y₂) := by
          change ((a₁ : Ω) * a₂) • (y₁ + y₂) = (a₂ : Ω) • ((a₁ : Ω) • y₁) + (a₁ : Ω) • ((a₂ : Ω) • y₂)
          rw [smul_add, smul_smul, smul_smul, mul_comm (a₂ : Ω)]
        rw [this]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
      | smul c z _ hz =>
        obtain ⟨a, ha, hz⟩ := hz
        obtain ⟨a', ha', hc⟩ := exists_isUnit_mul_mem h c
        refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
        have : ((a' * a : chartRing S x I) : Ω) • (c • z) =
            (⟨_, hc⟩ : chartRing S x I) • ((a : Ω) • z) := by
          change ((a' : Ω) * a) • ((c : Ω) • z) = ((a' : Ω) * c) • ((a : Ω) • z)
          rw [smul_smul, smul_smul, mul_assoc, mul_assoc, mul_comm (a : Ω)]
        rw [this]
        exact Submodule.smul_mem _ _ hz
    · rintro ⟨a, ⟨u, hu⟩, hay⟩
      have hJ := (M.tildeSys 0).mono I J h _ hay
      have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
        change y = ((↑u⁻¹ : chartRing S x J) : Ω) • ((a : Ω) • y)
        rw [smul_smul, hinv, one_smul]
      rw [hy]
      exact Submodule.smul_mem _ _ hJ

omit [IsScalarTower S Ω E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tildeFam_toSubSystem (M : FinGradedSub (S := S) (x := x) E) :
    (tildeFam M).toSubSystem = M.tildeSys 0 := rfl

omit [Module S E] [IsScalarTower S Ω E] in

/- English proof (translation)
Take `⟨T, hT⟩` from `hfg`. Establish `hsub : (singleChart hxi).1 ⊆ I.1` using `Finset.singleton_subset_iff.mpr hi`. Establish `key : ∀ z, z ∈ Submodule.span (chartRing S x (singleChart hxi)) (T : Set E) → z ∈ Submodule.span (chartRing S x I) (T : Set E)` using `fun z hz => by`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz => exact Submodule.subset_span hz`.

Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => exact Submodule.add_mem _ ha hb`. Consider the case `smul b z _ hz => exact Submodule.smul_mem _ (chartIncl hsub b) hz`. Use `⟨T, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`.

Introduce `y hy`. Conclude with `F.mono _ I hsub y (hT ▸ Submodule.subset_span hy)`. Introduce `y hy`. Take `⟨a, ⟨u, hu⟩, hay⟩` from `(F.mem_iff _ I hsub y).mp hy`. Rewrite `hay` using `[← hT]`.

Establish `h2` using `key _ hay`. Establish `hinv : ((↑u⁻¹ : chartRing S x I) : Ω) * (a : Ω) = 1`. Use `congrArg Subtype.val (Units.inv_mul u)` as an intermediate fact. Rewrite `this` using `[hu]`. Conclude with `this`.

Establish `hy' : y = (↑u⁻¹ : chartRing S x I) • ((a : Ω) • y)`. Express the relevant statement in the definitionally equal form `y = ((↑u⁻¹ : chartRing S x I) : Ω) • ((a : Ω) • y)`. Rewrite using `[smul_smul, hinv, one_smul]`. Rewrite using `[hy']`. Conclude with `Submodule.smul_mem _ _ h2`.
-/
theorem fg_of_single (F : SubFamily S x E) (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (hxi : x i ≠ 0)
    (hfg : (F.sub (singleChart hxi)).FG) : (F.sub I).FG := by
  obtain ⟨T, hT⟩ := hfg
  have hsub : (singleChart hxi).1 ⊆ I.1 := Finset.singleton_subset_iff.mpr hi
  have key : ∀ z, z ∈ Submodule.span (chartRing S x (singleChart hxi)) (T : Set E) →
      z ∈ Submodule.span (chartRing S x I) (T : Set E) := fun z hz => by
    induction hz using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span hz
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul b z _ hz => exact Submodule.smul_mem _ (chartIncl hsub b) hz
  refine ⟨T, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro y hy
    exact F.mono _ I hsub y (hT ▸ Submodule.subset_span hy)
  · intro y hy
    obtain ⟨a, ⟨u, hu⟩, hay⟩ := (F.mem_iff _ I hsub y).mp hy
    rw [← hT] at hay
    have h2 := key _ hay
    have hinv : ((↑u⁻¹ : chartRing S x I) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hy' : y = (↑u⁻¹ : chartRing S x I) • ((a : Ω) • y) := by
      change y = ((↑u⁻¹ : chartRing S x I) : Ω) • ((a : Ω) • y)
      rw [smul_smul, hinv, one_smul]
    rw [hy']
    exact Submodule.smul_mem _ _ h2

omit [Module S E] [IsScalarTower S Ω E] in

/- English proof (translation)
Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hi)`. Use `Domination.isNoetherianRing_chartRing (S := S) hxi` as an intermediate fact. Establish `: IsNoetherian (chartRing S x (singleChart hxi)) (F.sub (singleChart hxi))` using `isNoetherian_of_fg_of_noetherian _ (hF _)`. Conclude with `fg_of_single G I hi hxi (Submodule.FG.of_le_of_isNoetherian (hle _))`.
-/
theorem fg_of_le [IsNoetherianRing S] (F G : SubFamily S x E) (hF : ∀ I, (F.sub I).FG)
    (hle : ∀ I, G.sub I ≤ F.sub I) (I : Chart x) : (G.sub I).FG := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have := Domination.isNoetherianRing_chartRing (S := S) hxi
  have : IsNoetherian (chartRing S x (singleChart hxi)) (F.sub (singleChart hxi)) :=
    isNoetherian_of_fg_of_noetherian _ (hF _)
  exact fg_of_single G I hi hxi (Submodule.FG.of_le_of_isNoetherian (hle _))

end Tilde

section Graded

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

def gsup (M M' : FinGradedSub (S := S) (x := x) E) : FinGradedSub (S := S) (x := x) E where
  piece c := M.piece c ⊔ M'.piece c
  smul_mem d c f m hf hm := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
    rw [smul_add]
    exact Submodule.add_mem_sup (M.smul_mem d c f a hf ha) (M'.smul_mem d c f b hf hb)
  fg := by
    obtain ⟨n, deg, gen, hmem, hspan⟩ := M.fg
    obtain ⟨n', deg', gen', hmem', hspan'⟩ := M'.fg
    refine ⟨n + n', Fin.append deg deg', Fin.append gen gen', fun j => ?_, fun c => ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · rw [Fin.append_left, Fin.append_left]; exact Submodule.mem_sup_left (hmem j)
      · rw [Fin.append_right, Fin.append_right]; exact Submodule.mem_sup_right (hmem' j)
    · refine sup_le ((hspan c).trans (Submodule.span_mono ?_)) ((hspan' c).trans (Submodule.span_mono ?_))
      · rintro _ ⟨j, f, e, hf, he, rfl⟩
        exact ⟨Fin.castAdd n' j, f, e, hf, by rw [Fin.append_left]; exact he, by rw [Fin.append_left]⟩
      · rintro _ ⟨j, f, e, hf, he, rfl⟩
        exact ⟨Fin.natAdd n j, f, e, hf, by rw [Fin.append_right]; exact he, by rw [Fin.append_right]⟩

omit [IsScalarTower S Ω E] in

/- English proof (translation)
Use `le_antisymm (Submodule.span_le.mpr ?_) (sup_le (tilde_mono (fun _ => le_sup_left) c I) (tilde_mono (fun _ => le_sup_right) c I))` and prove the remaining obligations. Introduce and unpack `_ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩`. Take `⟨p, hp, q, hq, rfl⟩` from `Submodule.mem_sup.mp hm`. Rewrite using `[smul_add]`. Conclude with `Submodule.add_mem_sup (Submodule.subset_span ⟨p, s, a, e, hs, hse, hp, hae, rfl⟩) (Submodule.subset_span ⟨q, s, a, e, hs, hse, hq, hae, rfl⟩)`.
-/
theorem tilde_gsup (M M' : FinGradedSub (S := S) (x := x) E) (c : ℤ) (I : Chart x) :
    (gsup M M').tilde c I = M.tilde c I ⊔ M'.tilde c I := by
  refine le_antisymm (Submodule.span_le.mpr ?_)
    (sup_le (tilde_mono (fun _ => le_sup_left) c I) (tilde_mono (fun _ => le_sup_right) c I))
  rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hm
  rw [smul_add]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨p, s, a, e, hs, hse, hp, hae, rfl⟩)
    (Submodule.subset_span ⟨q, s, a, e, hs, hse, hq, hae, rfl⟩)

def gmul (M : FinGradedSub (S := S) (x := x) E) {s : ℕ} (h : Fin s → Poly S N) (d : Fin s → ℕ) :
    FinGradedSub (S := S) (x := x) E where
  piece c := Submodule.span S {z | ∃ (l : Fin s) (b : ℤ) (m : E), m ∈ M.piece b ∧ b + d l = c ∧
    z = aeval x (h l) • m}
  smul_mem e c f m hf hm := by
    induction hm using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, b, m, hm, hb, rfl⟩ := hz
      refine Submodule.subset_span ⟨l, b + e, aeval x f • m, M.smul_mem e b f m hf hm, by rw [← hb]; ring, ?_⟩
      rw [smul_comm]
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul r z _ hz => rw [smul_comm]; exact Submodule.smul_mem _ r hz
  fg := by
    obtain ⟨n, deg, gen, hmem, hspan⟩ := M.fg
    let q : Fin (s * n) ≃ Fin s × Fin n := finProdFinEquiv.symm
    refine ⟨s * n, fun k => deg (q k).2 + d (q k).1, fun k => aeval x (h (q k).1) • gen (q k).2,
      fun k => Submodule.subset_span ⟨(q k).1, deg (q k).2, gen (q k).2, hmem _, rfl, rfl⟩, fun c => ?_⟩
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, b, m, hm, hb, rfl⟩
    have key : ∀ z, z ∈ Submodule.span S {z | ∃ (j : Fin n) (f : Poly S N) (e : ℕ),
        f.IsHomogeneous e ∧ (e : ℤ) + deg j = b ∧ z = aeval x f • gen j} →
        aeval x (h l) • z ∈ Submodule.span S {z | ∃ (k : Fin (s * n)) (f : Poly S N) (e : ℕ),
          f.IsHomogeneous e ∧ (e : ℤ) + (deg (q k).2 + d (q k).1) = c ∧
            z = aeval x f • aeval x (h (q k).1) • gen (q k).2} := fun z hz => by
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨j, f, e, hf, he, rfl⟩ := hz
        refine Submodule.subset_span ⟨q.symm (l, j), f, e, hf, ?_, ?_⟩
        · rw [Equiv.apply_symm_apply]; rw [← hb, ← he]; ring
        · rw [Equiv.apply_symm_apply, smul_comm]
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
      | smul r z _ hz => rw [smul_comm]; exact Submodule.smul_mem _ r hz
    exact key m (hspan b hm)

/- English proof (translation)
Use `conv_lhs => rw [← sum_homogeneousComponent c, Finset.sum_mul, map_sum]`. Establish `each : ∀ i, homogeneousComponent n (homogeneousComponent i c * h) = if i + d = n then homogeneousComponent i c * h else 0` using `fun i => by`. Rewrite using `[homogeneousComponent_of_mem ((homogeneousComponent_isHomogeneous i c).mul hh)]`. Distinguish the cases in `hi : i + d = n`. Rewrite using `[if_pos hi.symm, if_pos hi]`.

Rewrite using `[if_neg (Ne.symm hi), if_neg hi]`. Repeatedly rewrite using `[each]`. Rewrite using `[Finset.sum_eq_single (n - d)]`. Distinguish the cases in `hdn : d ≤ n`. Rewrite using `[if_pos (by omega), if_pos hdn]`.

Rewrite using `[if_neg hdn]`. Distinguish the cases in `h0 : n - d + d = n`. It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h0]`.

Introduce `i _ hi`. Rewrite using `[if_neg (by omega)]`. Introduce `hn`. Distinguish the cases in `h0 : n - d + d = n`. Rewrite using `[if_pos h0, homogeneousComponent_eq_zero _ _ (by simp at hn; omega), zero_mul]`.

Rewrite using `[if_neg h0]`.
-/
theorem homogeneousComponent_mul_form (c h : Poly S N) {d : ℕ} (hh : h.IsHomogeneous d) (n : ℕ) :
    homogeneousComponent n (c * h) = if d ≤ n then homogeneousComponent (n - d) c * h else 0 := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent c, Finset.sum_mul, map_sum]
  have each : ∀ i, homogeneousComponent n (homogeneousComponent i c * h) =
      if i + d = n then homogeneousComponent i c * h else 0 := fun i => by
    rw [homogeneousComponent_of_mem ((homogeneousComponent_isHomogeneous i c).mul hh)]
    by_cases hi : i + d = n
    · rw [if_pos hi.symm, if_pos hi]
    · rw [if_neg (Ne.symm hi), if_neg hi]
  simp_rw [each]
  rw [Finset.sum_eq_single (n - d)]
  · by_cases hdn : d ≤ n
    · rw [if_pos (by omega), if_pos hdn]
    · rw [if_neg hdn]
      by_cases h0 : n - d + d = n
      · exfalso; omega
      · rw [if_neg h0]
  · intro i _ hi
    rw [if_neg (by omega)]
  · intro hn
    by_cases h0 : n - d + d = n
    · rw [if_pos h0, homogeneousComponent_eq_zero _ _ (by simp at hn; omega), zero_mul]
    · rw [if_neg h0]

/- English proof (translation)
Rewrite `hfJ` using `[← hJ]`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun _).mp hfJ`. Establish `hf' : f = ∑ l, (if d l ≤ e then homogeneousComponent (e - d l) (c l) * h l else 0)` using `by conv_lhs => rw [← homogeneousComponent_eq_self hf, ← hc, map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul, homogeneousComponent_mul_form _ _ (hh l)]`.

Rewrite using `[hf', map_sum, Finset.sum_smul]`. Use `Submodule.sum_mem _ fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hle : d l ≤ e`. Rewrite using `[if_pos hle, map_mul, mul_comm, mul_smul]`. Use `Submodule.subset_span ⟨l, a + ((e - d l : ℕ) : ℤ), _, M.smul_mem _ _ _ _ (homogeneousComponent_isHomogeneous _ _) hz, ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[Nat.cast_sub hle]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hle, map_zero, zero_smul]`. Conclude with `Submodule.zero_mem _`.
-/
theorem smul_mem_gmul (M : FinGradedSub (S := S) (x := x) E) {s : ℕ} (h : Fin s → Poly S N) (d : Fin s → ℕ)
    (hh : ∀ l, (h l).IsHomogeneous (d l)) {J : Ideal (Poly S N)} (hJ : Ideal.span (Set.range h) = J)
    {f : Poly S N} {e : ℕ} (hfJ : f ∈ J) (hf : f.IsHomogeneous e) {a : ℤ} {z : E} (hz : z ∈ M.piece a) :
    aeval x f • z ∈ (gmul M h d).piece (a + e) := by
  classical
  rw [← hJ] at hfJ
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hfJ
  have hf' : f = ∑ l, (if d l ≤ e then homogeneousComponent (e - d l) (c l) * h l else 0) := by
    conv_lhs => rw [← homogeneousComponent_eq_self hf, ← hc, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_eq_mul, homogeneousComponent_mul_form _ _ (hh l)]
  rw [hf', map_sum, Finset.sum_smul]
  refine Submodule.sum_mem _ fun l _ => ?_
  by_cases hle : d l ≤ e
  · rw [if_pos hle, map_mul, mul_comm, mul_smul]
    refine Submodule.subset_span ⟨l, a + ((e - d l : ℕ) : ℤ), _,
      M.smul_mem _ _ _ _ (homogeneousComponent_isHomogeneous _ _) hz, ?_, rfl⟩
    rw [Nat.cast_sub hle]; ring
  · rw [if_neg hle, map_zero, zero_smul]
    exact Submodule.zero_mem _

/- English proof (translation)
Take `⟨i, hi⟩` from `I.2.1`. Establish `hxi : x i ≠ 0` using `(mem_support x).mp (I.2.2 hi)`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨m, t, a, e, ht, hte, hm, hae, rfl⟩`. Establish `ht0` using `eval_ne_zero_of_mem_monos I ht`.

Express the relevant statement in the definitionally equal form `m ∈ Submodule.span S _ at hm`. Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨l, b, m, hm, hb, rfl⟩` from `hz`. Establish `hX0 : aeval x (X i ^ d l : Poly S N) ≠ 0`.

Rewrite using `[map_pow, aeval_X]`. Conclude with `pow_ne_zero _ hxi`. Establish `hq : aeval x (h l) / aeval x (X i ^ d l : Poly S N) ∈ (idealSys x J).sub I` using `Submodule.subset_span ⟨h l, X i ^ d l, d l, hJ l, pow_mem (X_mem_monos hi) _, hh l, isHomogeneous_X_pow i _, rfl⟩`. Establish `hy : (aeval x t)⁻¹ • (aeval x (X i ^ d l : Poly S N) • m) ∈ F.sub I`. Use `hF I (Submodule.subset_span ⟨_, t, a, e, ht, hte, ?_, hae, rfl⟩)` and prove the remaining obligations.

Use `M.smul_mem (d l) b (X i ^ d l) m (isHomogeneous_X_pow i _) hm` as an intermediate fact. Rewrite `this` using `[hb]`. Then use the resulting hypothesis. Use `Submodule.subset_span ⟨_, hq, _, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, smul_smul, smul_smul]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Consider the case `zero => rw [smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [smul_add]`. Conclude with `Submodule.add_mem _ ha hb`.

Consider the case `smul r z _ hz => rw [smul_comm]`. Conclude with `Submodule.smul_of_tower_mem _ r hz`.
-/
theorem tilde_gmul_le (M : FinGradedSub (S := S) (x := x) E) {s : ℕ} (h : Fin s → Poly S N) (d : Fin s → ℕ)
    (hh : ∀ l, (h l).IsHomogeneous (d l)) {J : Ideal (Poly S N)} (hJ : ∀ l, h l ∈ J) (F : SubSystem S x E)
    (hF : ∀ I, M.tilde 0 I ≤ F.sub I) (I : Chart x) :
    (gmul M h d).tilde 0 I ≤ (F.twist (idealSys x J)).sub I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, t, a, e, ht, hte, hm, hae, rfl⟩
  have ht0 := eval_ne_zero_of_mem_monos I ht
  change m ∈ Submodule.span S _ at hm
  induction hm using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨l, b, m, hm, hb, rfl⟩ := hz
    have hX0 : aeval x (X i ^ d l : Poly S N) ≠ 0 := by
      rw [map_pow, aeval_X]; exact pow_ne_zero _ hxi
    have hq : aeval x (h l) / aeval x (X i ^ d l : Poly S N) ∈ (idealSys x J).sub I :=
      Submodule.subset_span ⟨h l, X i ^ d l, d l, hJ l, pow_mem (X_mem_monos hi) _, hh l,
        isHomogeneous_X_pow i _, rfl⟩
    have hy : (aeval x t)⁻¹ • (aeval x (X i ^ d l : Poly S N) • m) ∈ F.sub I := by
      refine hF I (Submodule.subset_span ⟨_, t, a, e, ht, hte, ?_, hae, rfl⟩)
      have := M.smul_mem (d l) b (X i ^ d l) m (isHomogeneous_X_pow i _) hm
      rwa [hb] at this
    refine Submodule.subset_span ⟨_, hq, _, hy, ?_⟩
    rw [smul_smul, smul_smul, smul_smul]
    congr 1
    field_simp
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
  | smul r z _ hz => rw [smul_comm]; exact Submodule.smul_of_tower_mem _ r hz

/- English proof (translation)
Introduce `f hf` and use `by rw [← sum_homogeneousComponent f] exact Ideal.sum_mem _ fun i _ => h _ i (hJ f hf i) (homogeneousComponent_isHomogeneous i f)`.
-/
theorem le_of_forms {J P : Ideal (Poly S N)} (hJ : ∀ f ∈ J, ∀ d : ℕ, homogeneousComponent d f ∈ J)
    (h : ∀ (f : Poly S N) (e : ℕ), f ∈ J → f.IsHomogeneous e → f ∈ P) : J ≤ P := fun f hf => by
  rw [← sum_homogeneousComponent f]
  exact Ideal.sum_mem _ fun i _ => h _ i (hJ f hf i) (homogeneousComponent_isHomogeneous i f)

end Graded

end SnapperQuotFilt

end

end GroundTheory.Heights₂.Heights.Kleiman
