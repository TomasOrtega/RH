import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapInclKMemTwCentResOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigResIterateEqSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigIterateApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteLeftCosetRepresentativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerFiniteDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerDecompositionStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.TwOrbFin

section Generic

variable {H : Type} [Group H]

def Bnd (K₀ : Subgroup H) (D : Set H) : Prop := ∃ S : Finset H, ∀ d ∈ D, ∃ s ∈ S, ∃ k ∈ K₀, d = s * k

def Cmd (K₀ : Subgroup H) : Prop := ∀ s : H, ∃ S : Finset H, ∀ k ∈ K₀, ∃ s' ∈ S, ∃ k' ∈ K₀, k * s = s' * k'

variable {K₀ : Subgroup H}

/- English proof (translation)
Take `⟨S, hS⟩` from `hE`. Conclude with `⟨S, fun d hd => hS d (h hd)⟩`.
-/
theorem Bnd.mono {D E : Set H} (h : D ⊆ E) (hE : Bnd K₀ E) : Bnd K₀ D := by
  obtain ⟨S, hS⟩ := hE
  exact ⟨S, fun d hd => hS d (h hd)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨S, fun _ hd => hd⟩`.
-/
theorem bnd_finset (S : Finset H) : Bnd K₀ {g | ∃ s ∈ S, ∃ k ∈ K₀, g = s * k} :=
  ⟨S, fun _ hd => hd⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨{g}, fun d hd => ⟨g, Finset.mem_singleton_self _, 1, K₀.one_mem, by rw [hd, mul_one]⟩⟩`.
-/
theorem bnd_singleton (g : H) : Bnd K₀ {g} :=
  ⟨{g}, fun d hd => ⟨g, Finset.mem_singleton_self _, 1, K₀.one_mem, by rw [hd, mul_one]⟩⟩

/- English proof (translation)
Use `choose Sc hSc using hc`. Take `⟨S, hS⟩` from `hD`. Take `⟨T, hT⟩` from `hE`. Use `⟨S.biUnion fun s => T.biUnion fun t => (Sc t).image (s * ·), ?_⟩` and prove the remaining obligations. Introduce and unpack `g ⟨d, hd, e, he, rfl⟩`.

Take `⟨s, hs, k, hk, rfl⟩` from `hS d hd`. Take `⟨t, ht, l, hl, rfl⟩` from `hT e he`. Take `⟨s', hs', k', hk', e'⟩` from `hSc t k hk`. Use `⟨s * s', Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_biUnion.2 ⟨t, ht, Finset.mem_image.2 ⟨s', hs', rfl⟩⟩⟩, k' * l, K₀.mul_mem hk' hl, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem Bnd.mul (hc : Cmd K₀) {D E : Set H} (hD : Bnd K₀ D) (hE : Bnd K₀ E) :
    Bnd K₀ {g | ∃ d ∈ D, ∃ e ∈ E, g = d * e} := by
  choose Sc hSc using hc
  obtain ⟨S, hS⟩ := hD
  obtain ⟨T, hT⟩ := hE
  refine ⟨S.biUnion fun s => T.biUnion fun t => (Sc t).image (s * ·), ?_⟩
  rintro g ⟨d, hd, e, he, rfl⟩
  obtain ⟨s, hs, k, hk, rfl⟩ := hS d hd
  obtain ⟨t, ht, l, hl, rfl⟩ := hT e he
  obtain ⟨s', hs', k', hk', e'⟩ := hSc t k hk
  refine ⟨s * s', Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_biUnion.2 ⟨t, ht, Finset.mem_image.2 ⟨s', hs', rfl⟩⟩⟩,
    k' * l, K₀.mul_mem hk' hl, ?_⟩
  calc s * k * (t * l) = s * (k * t) * l := by group
    _ = _ := by rw [e']; group

/- English proof (translation)
Use `choose Sc hSc using hc`. Take `⟨S, hS⟩` from `hD`. Use `⟨S.biUnion fun s => Sc s⁻¹, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Take `⟨s, hs, k, hk, e⟩` from `hS _ hg`.

Take `⟨s', hs', k', hk', e'⟩` from `hSc s⁻¹ k⁻¹ (K₀.inv_mem hk)`. Use `⟨s', Finset.mem_biUnion.2 ⟨s, hs, hs'⟩, k', hk', ?_⟩` and prove the remaining obligations. Rewrite using `[← e', ← _root_.mul_inv_rev, ← e, inv_inv]`.
-/
theorem Bnd.inv (hc : Cmd K₀) {D : Set H} (hD : Bnd K₀ D) : Bnd K₀ {g | g⁻¹ ∈ D} := by
  choose Sc hSc using hc
  obtain ⟨S, hS⟩ := hD
  refine ⟨S.biUnion fun s => Sc s⁻¹, ?_⟩
  intro g hg
  obtain ⟨s, hs, k, hk, e⟩ := hS _ hg
  obtain ⟨s', hs', k', hk', e'⟩ := hSc s⁻¹ k⁻¹ (K₀.inv_mem hk)
  refine ⟨s', Finset.mem_biUnion.2 ⟨s, hs, hs'⟩, k', hk', ?_⟩
  rw [← e', ← _root_.mul_inv_rev, ← e, inv_inv]

/- English proof (translation)
Take `⟨S, hS⟩` from `hD`. Use `⟨S.image θ, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨d, hd, rfl⟩`. Take `⟨s, hs, k, hk, rfl⟩` from `hS d hd`. Conclude with `⟨θ s, Finset.mem_image.2 ⟨s, hs, rfl⟩, θ k, hθ k hk, map_mul θ s k⟩`.
-/
theorem Bnd.map (θ : H →* H) (hθ : ∀ k ∈ K₀, θ k ∈ K₀) {D : Set H} (hD : Bnd K₀ D) : Bnd K₀ (θ '' D) := by
  obtain ⟨S, hS⟩ := hD
  refine ⟨S.image θ, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨s, hs, k, hk, rfl⟩ := hS d hd
  exact ⟨θ s, Finset.mem_image.2 ⟨s, hs, rfl⟩, θ k, hθ k hk, map_mul θ s k⟩

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simpa using hD`. Consider the case `succ j ih`. Rewrite using `[Function.iterate_succ', Set.image_comp]`. Conclude with `ih.map θ hθ`.
-/
theorem Bnd.iterate (θ : H →* H) (hθ : ∀ k ∈ K₀, θ k ∈ K₀) (j : ℕ) {D : Set H} (hD : Bnd K₀ D) :
    Bnd K₀ ((⇑θ)^[j] '' D) := by
  induction j with
  | zero => simpa using hD
  | succ j ih =>
    rw [Function.iterate_succ', Set.image_comp]
    exact ih.map θ hθ

/- English proof (translation)
Simplify using `[nrmG, List.range_succ, List.map_append, List.prod_append]`.
-/
theorem nrmG_succ (θ : H →* H) (j : ℕ) (y : H) : nrmG θ (j + 1) y = nrmG θ j y * (⇑θ)^[j] y := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Use `(bnd_singleton 1).mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨d, -, rfl⟩`. Simplify using `[nrmG]`.

Consider the case `succ j ih`. Use `(ih.mul hc (hD.iterate θ hθ j)).mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨d, hd, rfl⟩`. Conclude with `⟨_, ⟨d, hd, rfl⟩, _, ⟨d, hd, rfl⟩, nrmG_succ θ j d⟩`.
-/
theorem Bnd.nrm (hc : Cmd K₀) (θ : H →* H) (hθ : ∀ k ∈ K₀, θ k ∈ K₀) (j : ℕ) {D : Set H} (hD : Bnd K₀ D) :
    Bnd K₀ (nrmG θ j '' D) := by
  induction j with
  | zero =>
    refine (bnd_singleton 1).mono ?_
    rintro _ ⟨d, -, rfl⟩
    simp [nrmG]
  | succ j ih =>
    refine (ih.mul hc (hD.iterate θ hθ j)).mono ?_
    rintro _ ⟨d, hd, rfl⟩
    exact ⟨_, ⟨d, hd, rfl⟩, _, ⟨d, hd, rfl⟩, nrmG_succ θ j d⟩

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp [nrmG]`. Consider the case `succ j ih`. Rewrite using `[nrmG_succ, nrmG_succ, ih, iterate_map_mul, iterate_map_mul, iterate_map_inv, ← Function.iterate_succ_apply θ j x]`. Use `group`.
-/
theorem nrmG_twConj (θ : H →* H) (j : ℕ) (x δ : H) :
    nrmG θ j (x⁻¹ * δ * θ x) = x⁻¹ * nrmG θ j δ * (⇑θ)^[j] x := by
  induction j with
  | zero => simp [nrmG]
  | succ j ih =>
    rw [nrmG_succ, nrmG_succ, ih, iterate_map_mul, iterate_map_mul, iterate_map_inv,
      ← Function.iterate_succ_apply θ j x]
    group

/- English proof (translation)
Take `⟨S, hS⟩` from `hD`. Use `haveI : (K.subgroupOf K₀).FiniteIndex := ⟨hK⟩`. Use `haveI : Finite (K₀ ⧸ K.subgroupOf K₀) := Subgroup.finite_quotient_of_finiteIndex`. Set `R : Set H` to `Set.range fun c : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out c : K₀) : H)`. Establish `hR : R.Finite` using `Set.finite_range _`.

Establish `hcov : ∀ k ∈ K₀, ∃ c ∈ R, ∃ l ∈ K, k = c * l`. Introduce `k hk`. Set `c : K₀ ⧸ K.subgroupOf K₀` to `QuotientGroup.mk ⟨k, hk⟩`. Establish `h1 : ((Quotient.out c : K₀))⁻¹ * ⟨k, hk⟩ ∈ K.subgroupOf K₀` using `QuotientGroup.leftRel_apply.mp (Quotient.exact' (Quotient.out_eq' c))`. Use `⟨((Quotient.out c : K₀) : H), ⟨c, rfl⟩, ((Quotient.out c : K₀) : H)⁻¹ * k, h1, by group⟩` and prove the remaining obligations.

Use `((S.finite_toSet.prod hR).image fun sc : H × H => DoubleCoset.mk T K (sc.1 * sc.2)).subset ?_` and prove the remaining obligations. Introduce `q hq`. Take `⟨t, ht, d, hd, hx⟩` from `hP _ hq`. Take `⟨s, hs, k, hk, rfl⟩` from `hS d hd`. Take `⟨c, hc, l, hl, rfl⟩` from `hcov k hk`.

Use `⟨(s, c), ⟨hs, hc⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← DoubleCoset.out_eq' T K q, DoubleCoset.eq]`. Conclude with `⟨t, ht, l, hl, by rw [hx]; group⟩`.
-/
theorem finite_of_bnd (T K : Subgroup H) (hK : K.relIndex K₀ ≠ 0) (D : Set H) (hD : Bnd K₀ D) (P : H → Prop)
    (hP : ∀ x, P x → ∃ t ∈ T, ∃ d ∈ D, x = t * d) :
    {q : DoubleCoset.Quotient (T : Set H) (K : Set H) | P (Quotient.out q)}.Finite := by
  obtain ⟨S, hS⟩ := hD
  haveI : (K.subgroupOf K₀).FiniteIndex := ⟨hK⟩
  haveI : Finite (K₀ ⧸ K.subgroupOf K₀) := Subgroup.finite_quotient_of_finiteIndex
  let R : Set H := Set.range fun c : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out c : K₀) : H)
  have hR : R.Finite := Set.finite_range _
  have hcov : ∀ k ∈ K₀, ∃ c ∈ R, ∃ l ∈ K, k = c * l := by
    intro k hk
    let c : K₀ ⧸ K.subgroupOf K₀ := QuotientGroup.mk ⟨k, hk⟩
    have h1 : ((Quotient.out c : K₀))⁻¹ * ⟨k, hk⟩ ∈ K.subgroupOf K₀ :=
      QuotientGroup.leftRel_apply.mp (Quotient.exact' (Quotient.out_eq' c))
    refine ⟨((Quotient.out c : K₀) : H), ⟨c, rfl⟩, ((Quotient.out c : K₀) : H)⁻¹ * k, h1, by group⟩
  refine ((S.finite_toSet.prod hR).image fun sc : H × H => DoubleCoset.mk T K (sc.1 * sc.2)).subset ?_
  intro q hq
  obtain ⟨t, ht, d, hd, hx⟩ := hP _ hq
  obtain ⟨s, hs, k, hk, rfl⟩ := hS d hd
  obtain ⟨c, hc, l, hl, rfl⟩ := hcov k hk
  refine ⟨(s, c), ⟨hs, hc⟩, ?_⟩
  rw [← DoubleCoset.out_eq' T K q, DoubleCoset.eq]
  exact ⟨t, ht, l, hl, by rw [hx]; group⟩

end Generic

/- English proof (translation)
Use `choose Sc hSc using hc`. Use `⟨S.biUnion Sc, ?_⟩` and prove the remaining obligations. Introduce and unpack `g ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩`. Take `⟨s', hs', k', hk', e⟩` from `hSc s k₁ hk₁`. Conclude with `⟨s', Finset.mem_biUnion.2 ⟨s, hs, hs'⟩, k' * k₂, K₀.mul_mem hk' hk₂, by rw [e, mul_assoc]⟩`.
-/
theorem bnd_dbl {H : Type} [Group H] {K₀ : Subgroup H} (hc : Cmd K₀) (S : Finset H) :
    Bnd K₀ {g | ∃ s ∈ S, ∃ k₁ ∈ K₀, ∃ k₂ ∈ K₀, g = k₁ * s * k₂} := by
  choose Sc hSc using hc
  refine ⟨S.biUnion Sc, ?_⟩
  rintro g ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩
  obtain ⟨s', hs', k', hk', e⟩ := hSc s k₁ hk₁
  exact ⟨s', Finset.mem_biUnion.2 ⟨s, hs, hs'⟩, k' * k₂, K₀.mul_mem hk' hk₂, by rw [e, mul_assoc]⟩

section Specific

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Proceed by induction on `k generalizing g with`. Consider the case `zero => rfl`. Consider the case `succ k ih`. Rewrite using `[Function.iterate_succ_apply, ih]`. Both sides reduce to the same expression.
-/
theorem sigG_iterate_apply (G : HTGroup p) (r k : ℕ) (g : Gr G r) :
    (⇑(sigG G r))^[k] g = ((⇑(GlobalTheory.LKLoc.sig p (Q0 p) 1 r))^[k] g.1,
      fun i => (⇑(sigRes p (G.Fw i) G.n r))^[k] (g.2 i)) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    rfl

/- English proof (translation)
Rewrite using `[sigG_iterate_apply]`. Use `Prod.ext ?_ (funext fun i => ?_)` and prove the remaining obligations. Conclude with `GlobalTheory.LKLoc.sig_iterate_r p (Q0 p) inferInstance 1 r hr g.1`. Conclude with `sigRes_iterate_eq_self p (G.Fw i) G.n r hr (g.2 i)`.
-/
theorem sigG_iterate_self (G : HTGroup p) {r : ℕ} (hr : 0 < r) (g : Gr G r) : (⇑(sigG G r))^[r] g = g := by
  rw [sigG_iterate_apply]
  refine Prod.ext ?_ (funext fun i => ?_)
  · exact GlobalTheory.LKLoc.sig_iterate_r p (Q0 p) inferInstance 1 r hr g.1
  · exact sigRes_iterate_eq_self p (G.Fw i) G.n r hr (g.2 i)

end Specific

/- English proof (translation)
Introduce `p _ G r γ δ z K φ hr hγ hN hT`. Take `⟨hcomm, -, -, S, hS⟩` from `hT`. Establish `hc : Cmd (KHT p G.m G.n r G.Fw)` using `fun s => GlobalTheory.T.finite_left_coset_representatives p G r hr s`. Establish `hσ0 : ∀ k ∈ KHT p G.m G.n r G.Fw, sigG G r k ∈ KHT p G.m G.n r G.Fw` using `fun k hk => GlobalTheory.LKRes.Model.sigHT_KHT p G.m G.n r G.Fw k hk`. Set `C : Set (Gr G r)` to `{g | φ g ≠ 0}`.

Establish `hC : Bnd (KHT p G.m G.n r G.Fw) C` using `(bnd_dbl hc S).mono fun g hg => by`. Take `⟨s, hs, k₁, hk₁, k₂, hk₂, e⟩` from `hS g hg`. Conclude with `⟨s, hs, k₁, hk₁, k₂, hk₂, e⟩`. Take `⟨E, hE⟩` from `hC.nrm hc (sigG G r) hσ0 r`. Take `⟨D₁, hD₁⟩` from `GlobalTheory.T.centralizer_finite_decomposition p G r hr γ hγ E`.

Set `A : Set (Gr G r)` to `{g | ∃ d ∈ D₁, ∃ k ∈ KHT p G.m G.n r G.Fw, g = z⁻¹ * d * k}`. Establish `hA : Bnd (KHT p G.m G.n r G.Fw) A`. Use `⟨D₁.image (z⁻¹ * ·), ?_⟩` and prove the remaining obligations. Introduce and unpack `g ⟨d, hd, k, hk, rfl⟩`. Conclude with `⟨z⁻¹ * d, Finset.mem_image.2 ⟨d, hd, rfl⟩, k, hk, rfl⟩`.

Take `⟨E₂, hE₂⟩` from `(hA.mul hc hC).mul hc ((hA.map (sigG G r) hσ0).inv hc)`. Take `⟨D₃, hD₃⟩` from `GlobalTheory.T.twisted_centralizer_decomposition p G r hr γ hγ δ z hN E₂`. Use `finite_of_bnd (K₀ := KHT p G.m G.n r G.Fw) (GlobalTheory.BCT.twCent (sigG G r) δ) K hcomm.1 _ ((bnd_finset D₃).mul hc hA) (fun x => φ (x⁻¹ * δ * sigG G r x) ≠ 0) ?_` and prove the remaining obligations. Introduce `x hx`. Establish `hy : nrmG (sigG G r) r (x⁻¹ * δ * sigG G r x) ∈ nrmG (sigG G r) r '' C` using `⟨_, hx, rfl⟩`.

Take `⟨e, he, k, hk, hek⟩` from `hE _ hy`. Establish `key : (z * x)⁻¹ * inclG G r γ * (z * x) = e * k`. Rewrite using `[← hek, nrmG_twConj, sigG_iterate_self G hr, hN]`. Use `group`. Take `⟨t, htc, d, hd, k₁, hk₁, hzx⟩` from `hD₁ (z * x) ⟨e, he, k, hk, key⟩`.

Establish `ht'c : z⁻¹ * t * z * nrmG (sigG G r) r δ = nrmG (sigG G r) r δ * (z⁻¹ * t * z)`. Rewrite using `[hN]`. Combine the equalities or inequalities in the displayed calculation. Establish `hxe : x = z⁻¹ * t * z * (z⁻¹ * d * k₁)`. Combine the equalities or inequalities in the displayed calculation.

Establish `ht' : z⁻¹ * t * z = x * (z⁻¹ * d * k₁)⁻¹` using `by rw [hxe]; group`. Establish `hmem : (z⁻¹ * t * z)⁻¹ * δ * sigG G r (z⁻¹ * t * z) ∈ {g | ∃ u ∈ {g | ∃ a ∈ A, ∃ c ∈ C, g = a * c}, ∃ v ∈ {g | g⁻¹ ∈ sigG G r '' A}, g = u * v}`. Use `⟨(z⁻¹ * d * k₁) * (x⁻¹ * δ * sigG G r x), ⟨_, ⟨d, hd, k₁, hk₁, rfl⟩, _, hx, rfl⟩, (sigG G r (z⁻¹ * d * k₁))⁻¹, ?_, ?_⟩` and prove the remaining obligations. Use `show ((sigG G r (z⁻¹ * d * k₁))⁻¹)⁻¹ ∈ sigG G r '' A`. Rewrite using `[inv_inv]`.

Conclude with `⟨_, ⟨d, hd, k₁, hk₁, rfl⟩, rfl⟩`. Rewrite using `[ht', map_mul, map_inv]`. Use `group`. Take `⟨e₂, he₂, k₂, hk₂, h₂⟩` from `hE₂ _ hmem`. Take `⟨u, hu, d₃, hd₃, k₃, hk₃, hu'⟩` from `hD₃ _ ht'c ⟨e₂, he₂, k₂, hk₂, h₂⟩`.

Use `⟨u, hu, d₃ * k₃ * (z⁻¹ * d * k₁), ⟨d₃ * k₃, ⟨d₃, hd₃, k₃, hk₃, rfl⟩, _, ⟨d, hd, k₁, hk₁, rfl⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hxe, hu']`. Use `group`.
-/
theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (γ : Gp G) (δ z : Gr G r) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → regular₂ G γ → IsNrm G r γ δ z → IsTest (sigG G r) (KHT p G.m G.n r G.Fw) K φ → {q : DoubleCoset.Quotient (GlobalTheory.BCT.twCent (sigG G r) δ : Set (Gr G r)) (K : Set (Gr G r)) | φ ((Quotient.out q)⁻¹ * δ * sigG G r (Quotient.out q)) ≠ 0}.Finite := by
  intro p _ G r γ δ z K φ hr hγ hN hT
  obtain ⟨hcomm, -, -, S, hS⟩ := hT
  have hc : Cmd (KHT p G.m G.n r G.Fw) := fun s => GlobalTheory.T.finite_left_coset_representatives p G r hr s
  have hσ0 : ∀ k ∈ KHT p G.m G.n r G.Fw, sigG G r k ∈ KHT p G.m G.n r G.Fw :=
    fun k hk => GlobalTheory.LKRes.Model.sigHT_KHT p G.m G.n r G.Fw k hk
  let C : Set (Gr G r) := {g | φ g ≠ 0}
  have hC : Bnd (KHT p G.m G.n r G.Fw) C := (bnd_dbl hc S).mono fun g hg => by
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, e⟩ := hS g hg
    exact ⟨s, hs, k₁, hk₁, k₂, hk₂, e⟩
  obtain ⟨E, hE⟩ := hC.nrm hc (sigG G r) hσ0 r
  obtain ⟨D₁, hD₁⟩ := GlobalTheory.T.centralizer_finite_decomposition p G r hr γ hγ E
  let A : Set (Gr G r) := {g | ∃ d ∈ D₁, ∃ k ∈ KHT p G.m G.n r G.Fw, g = z⁻¹ * d * k}
  have hA : Bnd (KHT p G.m G.n r G.Fw) A := by
    refine ⟨D₁.image (z⁻¹ * ·), ?_⟩
    rintro g ⟨d, hd, k, hk, rfl⟩
    exact ⟨z⁻¹ * d, Finset.mem_image.2 ⟨d, hd, rfl⟩, k, hk, rfl⟩
  obtain ⟨E₂, hE₂⟩ := (hA.mul hc hC).mul hc ((hA.map (sigG G r) hσ0).inv hc)
  obtain ⟨D₃, hD₃⟩ := GlobalTheory.T.twisted_centralizer_decomposition p G r hr γ hγ δ z hN E₂
  refine finite_of_bnd (K₀ := KHT p G.m G.n r G.Fw) (GlobalTheory.BCT.twCent (sigG G r) δ) K hcomm.1 _
    ((bnd_finset D₃).mul hc hA) (fun x => φ (x⁻¹ * δ * sigG G r x) ≠ 0) ?_
  intro x hx
  have hy : nrmG (sigG G r) r (x⁻¹ * δ * sigG G r x) ∈ nrmG (sigG G r) r '' C := ⟨_, hx, rfl⟩
  obtain ⟨e, he, k, hk, hek⟩ := hE _ hy
  have key : (z * x)⁻¹ * inclG G r γ * (z * x) = e * k := by
    rw [← hek, nrmG_twConj, sigG_iterate_self G hr, hN]; group
  obtain ⟨t, htc, d, hd, k₁, hk₁, hzx⟩ := hD₁ (z * x) ⟨e, he, k, hk, key⟩
  have ht'c : z⁻¹ * t * z * nrmG (sigG G r) r δ = nrmG (sigG G r) r δ * (z⁻¹ * t * z) := by
    rw [hN]
    calc z⁻¹ * t * z * (z⁻¹ * inclG G r γ * z) = z⁻¹ * (t * inclG G r γ) * z := by group
      _ = z⁻¹ * (inclG G r γ * t) * z := by rw [htc]
      _ = _ := by group
  have hxe : x = z⁻¹ * t * z * (z⁻¹ * d * k₁) := by
    calc x = z⁻¹ * (z * x) := by group
      _ = _ := by rw [hzx]; group
  have ht' : z⁻¹ * t * z = x * (z⁻¹ * d * k₁)⁻¹ := by rw [hxe]; group
  have hmem : (z⁻¹ * t * z)⁻¹ * δ * sigG G r (z⁻¹ * t * z) ∈
      {g | ∃ u ∈ {g | ∃ a ∈ A, ∃ c ∈ C, g = a * c}, ∃ v ∈ {g | g⁻¹ ∈ sigG G r '' A}, g = u * v} := by
    refine ⟨(z⁻¹ * d * k₁) * (x⁻¹ * δ * sigG G r x), ⟨_, ⟨d, hd, k₁, hk₁, rfl⟩, _, hx, rfl⟩,
      (sigG G r (z⁻¹ * d * k₁))⁻¹, ?_, ?_⟩
    · show ((sigG G r (z⁻¹ * d * k₁))⁻¹)⁻¹ ∈ sigG G r '' A
      rw [inv_inv]
      exact ⟨_, ⟨d, hd, k₁, hk₁, rfl⟩, rfl⟩
    · rw [ht', map_mul, map_inv]; group
  obtain ⟨e₂, he₂, k₂, hk₂, h₂⟩ := hE₂ _ hmem
  obtain ⟨u, hu, d₃, hd₃, k₃, hk₃, hu'⟩ := hD₃ _ ht'c ⟨e₂, he₂, k₂, hk₂, h₂⟩
  refine ⟨u, hu, d₃ * k₃ * (z⁻¹ * d * k₁), ⟨d₃ * k₃, ⟨d₃, hd₃, k₃, hk₃, rfl⟩, _, ⟨d, hd, k₁, hk₁, rfl⟩, rfl⟩, ?_⟩
  rw [hxe, hu']; group

end GlobalTheory.TwOrbFin
