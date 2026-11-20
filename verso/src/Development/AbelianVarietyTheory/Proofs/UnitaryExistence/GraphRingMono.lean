import Mathlib
open IsLocalRing Polynomial

namespace GlobalTheory.PBasis

variable {k : Type} [Field k]

def graphRing (p : ℕ) {Q : Type} [CommRing Q] (f : k →+* Q) (g : k → Q) (B : Set k) :
    Subring (k × Q) :=
  Subring.closure (Set.range (fun x : k => (x ^ p, f x)) ∪ (fun b => (b, g b)) '' B)

def Indep (p : ℕ) (B : Set k) : Prop :=
  ∀ (Q : Type) [CommRing Q] (f : k →+* Q) (g : k → Q), (∀ b ∈ B, g b ^ p = f b) →
    ∀ z ∈ graphRing p f g B, z.1 = 0 → z.2 = 0

/- English proof (translation)
The claim follows from `Subring.closure_mono (Set.union_subset_union_right _ (Set.image_mono h))`.
-/
lemma graphRing_mono (p : ℕ) {Q : Type} [CommRing Q] (f : k →+* Q) (g : k → Q) {B C : Set k}
    (h : B ⊆ C) : graphRing p f g B ≤ graphRing p f g C :=
  Subring.closure_mono (Set.union_subset_union_right _ (Set.image_mono h))

/- English proof (translation)
Unfold `graphRing`. Rewrite using `[RingHom.map_closure, Set.image_union, ← Set.range_comp, Set.image_image]`. Use `congr 2`. Simplify using the standard rewrite rules.
-/
lemma map_graphRing (p : ℕ) {Q : Type} [CommRing Q] (f : k →+* Q) (g : k → Q) (B : Set k) :
    (graphRing p f g B).map (RingHom.fst k Q) =
      Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) := by
  unfold graphRing
  rw [RingHom.map_closure, Set.image_union, ← Set.range_comp, Set.image_image]
  congr 2
  simp

/- English proof (translation)
Use `haveI := Fact.mk hp`. Use `haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 h0`. Introduce `Q _ f g _ z hz h1`. Establish `: graphRing p f g ∅ ≤ ((frobenius k p).prod f).range`. Unfold `graphRing`.

Rewrite using `[Subring.closure_le]`. Introduce and unpack `_ (⟨x, rfl⟩ | ⟨x, hx, _⟩)`. Conclude with `⟨x, by simp [frobenius_def]⟩`. Conclude with `hx.elim`. Take `⟨x, rfl⟩` from `this hz`.

Establish `hx : x ^ p = 0` using `by simpa [frobenius_def] using h1`. Establish `: x = 0` using `pow_eq_zero_iff hp.ne_zero |>.1 hx`. Simplify using `[this]`.
-/
lemma indep_empty {p : ℕ} (hp : p.Prime) (h0 : (p : k) = 0) : Indep p (∅ : Set k) := by
  haveI := Fact.mk hp
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 h0
  intro Q _ f g _ z hz h1
  have : graphRing p f g ∅ ≤ ((frobenius k p).prod f).range := by
    unfold graphRing
    rw [Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨x, hx, _⟩)
    · exact ⟨x, by simp [frobenius_def]⟩
    · exact hx.elim
  obtain ⟨x, rfl⟩ := this hz
  have hx : x ^ p = 0 := by simpa [frobenius_def] using h1
  have : x = 0 := pow_eq_zero_iff hp.ne_zero |>.1 hx
  simp [this]

/- English proof (translation)
Introduce `Q _ f g hg z hz h1`. Use `haveI : Nonempty c := hne.to_subtype`. Establish `hdir : Directed (· ≤ ·) (fun B : c => graphRing p f g B.1)`. Introduce `B C`. Break down `hc.total B.2 C.2 with h | h` into its components or cases.

Conclude with `⟨C, graphRing_mono p f g h, le_rfl⟩`. Conclude with `⟨B, le_rfl, graphRing_mono p f g h⟩`. Establish `: graphRing p f g (⋃₀ c) ≤ ⨆ B : c, graphRing p f g B.1`. Rewrite using `[graphRing, Subring.closure_le]`. Introduce and unpack `_ (⟨x, rfl⟩ | ⟨x, ⟨B, hB, hx⟩, rfl⟩)`.

Take `⟨B, hB⟩` from `hne`. Conclude with `le_iSup (fun B : c => graphRing p f g B.1) ⟨B, hB⟩ (Subring.subset_closure (Or.inl ⟨x, rfl⟩))`. Conclude with `le_iSup (fun B : c => graphRing p f g B.1) ⟨B, hB⟩ (Subring.subset_closure (Or.inr ⟨x, hx, rfl⟩))`. Take `⟨B, hB⟩` from `(Subring.mem_iSup_of_directed hdir).1 (this hz)`. Conclude with `h B.1 B.2 Q f g (fun b hb => hg b ⟨B.1, B.2, hb⟩) z hB h1`.
-/
lemma indep_sUnion (p : ℕ) (c : Set (Set k)) (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (h : ∀ B ∈ c, Indep p B) : Indep p (⋃₀ c) := by
  intro Q _ f g hg z hz h1
  haveI : Nonempty c := hne.to_subtype
  have hdir : Directed (· ≤ ·) (fun B : c => graphRing p f g B.1) := by
    intro B C
    rcases hc.total B.2 C.2 with h | h
    · exact ⟨C, graphRing_mono p f g h, le_rfl⟩
    · exact ⟨B, le_rfl, graphRing_mono p f g h⟩
  have : graphRing p f g (⋃₀ c) ≤ ⨆ B : c, graphRing p f g B.1 := by
    rw [graphRing, Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨x, ⟨B, hB, hx⟩, rfl⟩)
    · obtain ⟨B, hB⟩ := hne
      exact le_iSup (fun B : c => graphRing p f g B.1) ⟨B, hB⟩
        (Subring.subset_closure (Or.inl ⟨x, rfl⟩))
    · exact le_iSup (fun B : c => graphRing p f g B.1) ⟨B, hB⟩
        (Subring.subset_closure (Or.inr ⟨x, hx, rfl⟩))
  obtain ⟨B, hB⟩ := (Subring.mem_iSup_of_directed hdir).1 (this hz)
  exact h B.1 B.2 Q f g (fun b hb => hg b ⟨B.1, B.2, hb⟩) z hB h1

def powField {p : ℕ} (hp : p ≠ 0) (B : Set k) : Subfield k where
  toSubring := Subring.closure (Set.range (fun x : k => x ^ p) ∪ B)
  inv_mem' := by
    intro x hx
    change x ∈ Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) at hx
    change x⁻¹ ∈ Subring.closure (Set.range (fun x : k => x ^ p) ∪ B)
    rcases eq_or_ne x 0 with rfl | hx0
    · simpa using hx
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
    have : x⁻¹ = x ^ n * (x⁻¹) ^ (n + 1) := by
      rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hx0]; simp
    rw [this]
    exact mul_mem (pow_mem hx n) (Subring.subset_closure (Or.inl ⟨x⁻¹, rfl⟩))

/- English proof (translation)
Use `haveI := Fact.mk hp`. Use `haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 h0`. Introduce `Q _ f g hg z hz h1`. Establish `hga : g a ^ p = f a` using `hg a (Set.mem_insert _ _)`. Establish `hI` using `hB Q f g (fun b hb => hg b (Set.mem_insert_of_mem _ hb))`.

Use `set S := graphRing p f g B with hS`. Set `K` to `powField hp.ne_zero B`. Establish `hK : ∀ s : S, (s : k × Q).1 ∈ K`. Introduce `s`. Express the relevant statement in the definitionally equal form `_ ∈ Subring.closure (Set.range (fun x : k => x ^ p) ∪ B)`.

Rewrite using `[← map_graphRing p f g B]`. Conclude with `⟨s, s.2, rfl⟩`. Set `ψ : S →+* K` to `((RingHom.fst k Q).comp S.subtype).codRestrict K hK`. Establish `hψ : Function.Injective ψ`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `s hs`. Establish `h1 : (s : k × Q).1 = 0` using `congrArg Subtype.val hs`. Conclude with `Subtype.ext (Prod.ext h1 (hI s s.2 h1))`. Set `ev : S[X] →+* k × Q` to `eval₂RingHom S.subtype (a, g a)`. Establish `hle : graphRing p f g (insert a B) ≤ ev.range`.

Rewrite using `[graphRing, Subring.closure_le]`. Introduce and unpack `_ (⟨x, rfl⟩ | ⟨x, rfl | hx, rfl⟩)`. Conclude with `⟨C ⟨_, Subring.subset_closure (Or.inl ⟨x, rfl⟩)⟩, by simp [ev]⟩`. Conclude with `⟨X, by simp [ev]⟩`. Conclude with `⟨C ⟨_, Subring.subset_closure (Or.inr ⟨x, hx, rfl⟩)⟩, by simp [ev]⟩`.

Take `⟨P, rfl⟩` from `hle hz`. Set `c : S` to `⟨(a ^ p, f a), Subring.subset_closure (Or.inl ⟨a, rfl⟩)⟩`. Establish `hq : (X ^ p - C c : S[X]).Monic` using `monic_X_pow_sub_C c hp.ne_zero`. Establish `hevq : ev (X ^ p - C c) = 0`. Simplify using `[ev, c, hga]`.

Establish `hR : ev (P %ₘ (X ^ p - C c)) = ev P` using `by conv_rhs => rw [← modByMonic_add_div P (X ^ p - C c)]`. Rewrite using `[map_add, map_mul, hevq, zero_mul, add_zero]`. Establish `hirr : Irreducible (X ^ p - C (ψ c) : K[X])`. Apply `X_pow_sub_C_irreducible_of_prime hp` to reduce the goal to its premises. Introduce `b hb`.

Establish `h2 : (b : k) ^ p = a ^ p` using `congrArg Subtype.val hb`. Establish `h3 : (b : k) = a` using `frobenius_inj k p h2`. Conclude with `ha (h3 ▸ b.2)`. Establish `haev : ∀ T : S[X], aeval a (T.map ψ) = (ev T).1`. Introduce `T`.

Rewrite using `[aeval_def, eval₂_map]`. Express the relevant statement in the definitionally equal form `_ = RingHom.fst k Q (eval₂ S.subtype (a, g a) T)`. Rewrite using `[hom_eval₂]`. Both sides reduce to the same expression. Establish `hmapq : (X ^ p - C c : S[X]).map ψ = X ^ p - C (ψ c)` using `by simp`.

Establish `hmin : X ^ p - C (ψ c) = minpoly K a` using `minpoly.eq_of_irreducible_of_monic hirr (by rw [← hmapq, haev, hevq]; rfl) (monic_X_pow_sub_C _ hp.ne_zero)`. Establish `hdvd : (X ^ p - C c : S[X]).map ψ ∣ (P %ₘ (X ^ p - C c)).map ψ`. Rewrite using `[hmapq, hmin]`. Conclude with `minpoly.dvd K a (by rw [haev, hR, h1])`. Use `haveI : Nontrivial S := ψ.domain_nontrivial`.

Establish `hz0 : (P %ₘ (X ^ p - C c)).map ψ = 0`. Apply `eq_zero_of_dvd_of_degree_lt hdvd` to reduce the goal to its premises. Rewrite using `[degree_map_eq_of_injective hψ, degree_map_eq_of_injective hψ]`. Conclude with `degree_modByMonic_lt P hq`. Rewrite `hz0` using `[Polynomial.map_eq_zero_iff hψ]`.

Rewrite using `[← hR, hz0, map_zero]`. Both sides reduce to the same expression.
-/
lemma indep_insert {p : ℕ} (hp : p.Prime) (h0 : (p : k) = 0) {B : Set k} (hB : Indep p B) {a : k}
    (ha : a ∉ Subring.closure (Set.range (fun x : k => x ^ p) ∪ B)) : Indep p (insert a B) := by
  haveI := Fact.mk hp
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 h0
  intro Q _ f g hg z hz h1
  have hga : g a ^ p = f a := hg a (Set.mem_insert _ _)
  have hI := hB Q f g (fun b hb => hg b (Set.mem_insert_of_mem _ hb))
  set S := graphRing p f g B with hS
  let K := powField hp.ne_zero B
  have hK : ∀ s : S, (s : k × Q).1 ∈ K := by
    intro s
    change _ ∈ Subring.closure (Set.range (fun x : k => x ^ p) ∪ B)
    rw [← map_graphRing p f g B]
    exact ⟨s, s.2, rfl⟩
  let ψ : S →+* K := ((RingHom.fst k Q).comp S.subtype).codRestrict K hK
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    have h1 : (s : k × Q).1 = 0 := congrArg Subtype.val hs
    exact Subtype.ext (Prod.ext h1 (hI s s.2 h1))
  let ev : S[X] →+* k × Q := eval₂RingHom S.subtype (a, g a)
  have hle : graphRing p f g (insert a B) ≤ ev.range := by
    rw [graphRing, Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨x, rfl | hx, rfl⟩)
    · exact ⟨C ⟨_, Subring.subset_closure (Or.inl ⟨x, rfl⟩)⟩, by simp [ev]⟩
    · exact ⟨X, by simp [ev]⟩
    · exact ⟨C ⟨_, Subring.subset_closure (Or.inr ⟨x, hx, rfl⟩)⟩, by simp [ev]⟩
  obtain ⟨P, rfl⟩ := hle hz
  let c : S := ⟨(a ^ p, f a), Subring.subset_closure (Or.inl ⟨a, rfl⟩)⟩
  have hq : (X ^ p - C c : S[X]).Monic := monic_X_pow_sub_C c hp.ne_zero
  have hevq : ev (X ^ p - C c) = 0 := by
    simp [ev, c, hga]
  have hR : ev (P %ₘ (X ^ p - C c)) = ev P := by
    conv_rhs => rw [← modByMonic_add_div P (X ^ p - C c)]
    rw [map_add, map_mul, hevq, zero_mul, add_zero]
  have hirr : Irreducible (X ^ p - C (ψ c) : K[X]) := by
    apply X_pow_sub_C_irreducible_of_prime hp
    intro b hb
    have h2 : (b : k) ^ p = a ^ p := congrArg Subtype.val hb
    have h3 : (b : k) = a := frobenius_inj k p h2
    exact ha (h3 ▸ b.2)
  have haev : ∀ T : S[X], aeval a (T.map ψ) = (ev T).1 := by
    intro T
    rw [aeval_def, eval₂_map]
    change _ = RingHom.fst k Q (eval₂ S.subtype (a, g a) T)
    rw [hom_eval₂]
    rfl
  have hmapq : (X ^ p - C c : S[X]).map ψ = X ^ p - C (ψ c) := by simp
  have hmin : X ^ p - C (ψ c) = minpoly K a :=
    minpoly.eq_of_irreducible_of_monic hirr (by rw [← hmapq, haev, hevq]; rfl)
      (monic_X_pow_sub_C _ hp.ne_zero)
  have hdvd : (X ^ p - C c : S[X]).map ψ ∣ (P %ₘ (X ^ p - C c)).map ψ := by
    rw [hmapq, hmin]
    exact minpoly.dvd K a (by rw [haev, hR, h1])
  haveI : Nontrivial S := ψ.domain_nontrivial
  have hz0 : (P %ₘ (X ^ p - C c)).map ψ = 0 := by
    apply eq_zero_of_dvd_of_degree_lt hdvd
    rw [degree_map_eq_of_injective hψ, degree_map_eq_of_injective hψ]
    exact degree_modByMonic_lt P hq
  rw [Polynomial.map_eq_zero_iff hψ] at hz0
  rw [← hR, hz0, map_zero]
  rfl

/- English proof (translation)
Introduce `k _ p hp h0`. Take `⟨B, -, hB⟩` from `zorn_subset_nonempty {B : Set k | Indep p B} (fun c hc hch hne => ⟨⋃₀ c, indep_sUnion p c hch hne hc, fun s hs => Set.subset_sUnion_of_mem hs⟩) ∅ (indep_empty hp h0)`. Establish `htop : Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `a _`.

Assume the negation of the conclusion as `ha`. Use `hB.le_of_ge (indep_insert hp h0 hB.prop ha) (Set.subset_insert a B)` as an intermediate fact. Conclude with `ha (Subring.subset_closure (Or.inr (this (Set.mem_insert a B))))`. Use `⟨B, htop, fun Q _ f g hg => ?_⟩` and prove the remaining obligations. Establish `hI` using `hB.prop Q f g hg`.

Use `set S := graphRing p f g B with hS`. Set `φ : S →+* k` to `(RingHom.fst k Q).comp S.subtype`. Establish `hφ : Function.Bijective φ`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `s hs`. Conclude with `Subtype.ext (Prod.ext hs (hI s s.2 hs))`. Introduce `x`. Establish `: x ∈ S.map (RingHom.fst k Q)`. Rewrite using `[hS, map_graphRing, htop]`.

Discharge the goal by the elementary cases of `trivial`. Take `⟨s, hs, rfl⟩` from `this`. Conclude with `⟨⟨s, hs⟩, rfl⟩`. Set `e` to `RingEquiv.ofBijective φ hφ`. Establish `key : ∀ s : S, ((RingHom.snd k Q).comp S.subtype).comp e.symm.toRingHom (s : k × Q).1 = (s : k × Q).2`.

Introduce `s`. Establish `: e.symm (s : k × Q).1 = s` using `e.symm_apply_apply s`. Express the relevant statement in the definitionally equal form `((e.symm (s : k × Q).1 : S) : k × Q).2 = _`. Rewrite using `[this]`. Use `⟨((RingHom.snd k Q).comp S.subtype).comp e.symm.toRingHom, fun x => ?_, fun b hb => ?_⟩` and prove the remaining obligations.

Conclude with `key ⟨(x ^ p, f x), Subring.subset_closure (Or.inl ⟨x, rfl⟩)⟩`. Conclude with `key ⟨(b, g b), Subring.subset_closure (Or.inr ⟨b, hb, rfl⟩)⟩`.
-/
theorem exists_pBasis : ∀ (k : Type) [Field k] (p : ℕ), p.Prime → (p : k) = 0 → ∃ B : Set k, Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) = ⊤ ∧ ∀ (Q : Type) [CommRing Q] (f : k →+* Q) (g : k → Q), (∀ b ∈ B, g b ^ p = f b) → ∃ σ : k →+* Q, (∀ x, σ (x ^ p) = f x) ∧ ∀ b ∈ B, σ b = g b := by
  intro k _ p hp h0
  obtain ⟨B, -, hB⟩ := zorn_subset_nonempty {B : Set k | Indep p B}
    (fun c hc hch hne => ⟨⋃₀ c, indep_sUnion p c hch hne hc, fun s hs => Set.subset_sUnion_of_mem hs⟩)
    ∅ (indep_empty hp h0)
  have htop : Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) = ⊤ := by
    rw [eq_top_iff]
    intro a _
    by_contra ha
    have := hB.le_of_ge (indep_insert hp h0 hB.prop ha) (Set.subset_insert a B)
    exact ha (Subring.subset_closure (Or.inr (this (Set.mem_insert a B))))
  refine ⟨B, htop, fun Q _ f g hg => ?_⟩
  have hI := hB.prop Q f g hg
  set S := graphRing p f g B with hS
  let φ : S →+* k := (RingHom.fst k Q).comp S.subtype
  have hφ : Function.Bijective φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro s hs
      exact Subtype.ext (Prod.ext hs (hI s s.2 hs))
    · intro x
      have : x ∈ S.map (RingHom.fst k Q) := by
        rw [hS, map_graphRing, htop]; trivial
      obtain ⟨s, hs, rfl⟩ := this
      exact ⟨⟨s, hs⟩, rfl⟩
  let e := RingEquiv.ofBijective φ hφ
  have key : ∀ s : S, ((RingHom.snd k Q).comp S.subtype).comp e.symm.toRingHom (s : k × Q).1 = (s : k × Q).2 := by
    intro s
    have : e.symm (s : k × Q).1 = s := e.symm_apply_apply s
    change ((e.symm (s : k × Q).1 : S) : k × Q).2 = _
    rw [this]
  refine ⟨((RingHom.snd k Q).comp S.subtype).comp e.symm.toRingHom, fun x => ?_, fun b hb => ?_⟩
  · exact key ⟨(x ^ p, f x), Subring.subset_closure (Or.inl ⟨x, rfl⟩)⟩
  · exact key ⟨(b, g b), Subring.subset_closure (Or.inr ⟨b, hb, rfl⟩)⟩

end GlobalTheory.PBasis
