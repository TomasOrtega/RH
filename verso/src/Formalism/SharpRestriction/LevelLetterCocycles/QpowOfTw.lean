import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace Formalism.MainNotions.N

def WildTriv : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ), l.Prime →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → v ∉ placesOver E l →
    ∀ (M : Type) [Group M] (φ : G E Ω →* M), IsOpen (φ.ker : Set (G E Ω)) → (∀ g, ∃ n : ℕ, φ g ^ (l ^ n) = 1) →
    ∀ σ : G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) → φ σ = 1

/- English proof (translation)
Introduce `v hv g hg`. Establish `hS : v ∉ D.nd.S i` using `fun h => Finset.disjoint_left.1 (D.nd.SQ_disj i) h hv`. Establish `hl : v ∉ placesOver D.host.E (D.nd.l i)` using `D.nd.SQ_l i v (Or.inr hv)`. Establish `hgk : ∀ k, v ∉ placesOver D.host.E (D.host.g k)`. Introduce `k hk`.

Apply `hS` to reduce the goal to its premises. Rewrite using `[D.nd.S_def i v]`. Use `⟨?_, hl⟩` and prove the remaining obligations. Use `fin_cases k`. Conclude with `Or.inl hk`.

Conclude with `Or.inr (Or.inl hk)`. Establish `hpd : v ∉ D.ntw.pD (D.ntw.twOf i)`. Introduce `hp`. Establish `h' : v ∈ ((D.ntw.pD (D.ntw.twOf i) : Finset _) : Set (HeightOneSpectrum (𝓞 D.host.E)))` using `hp`. Rewrite `h'` using `[D.ntw.pD_eq, D.ntw.twOf_l]`.

Conclude with `hS ((D.nd.S_def i v).2 ⟨Or.inr (Or.inr h'), hl⟩)`. Establish `hl' : v ∉ placesOver D.host.E (D.ntw.l (D.ntw.twOf i))`. Rewrite using `[D.ntw.twOf_l]`. Conclude with `hl`. Establish `hchi : ∀ h ∈ Ine (F` using `D.host.E) (D.nd.plOm.1 v), D.nd.chi i 1 h = D.ntw.psiL i h := by`.

Introduce `h hh`. Establish `h1` using `D.ntw.twistCharacterFamily_unramified (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) v hl' hgk hpd (D.nd.plOm.1 v) (D.nd.plOm.2 v) h hh`. Rewrite using `[D.ntw.chi_tw i, MonoidHom.mul_apply, MonoidHom.comp_apply, h1, map_one, one_mul]`. Rewrite using `[hchi g hg, hchi _ (D.nd.locNd_chebotarevPlace_mem i v)]`. Take `⟨m, hm⟩` from `D.ntw.psiL_ord i (D.nd.gam0 i v)`.

Establish `hL : 1 ≤ D.nd.l i ^ m` using `Nat.one_le_pow _ _ (Fact.out : (D.nd.l i).Prime).pos`. Set `H : Subgroup (G D.host.E D.nd.Om)` to `{ carrier := {x | ∃ n : ℕ, D.ntw.psiL i x = D.ntw.psiL i (D.nd.gam0 i v) ^ n} mul_mem' := by`. Introduce and unpack `a b ⟨n, hn⟩ ⟨k, hk⟩`. Conclude with `⟨n + k, by rw [map_mul, hn, hk, pow_add]⟩`. Use the proof step `one_mem' := ⟨0, by rw [map_one, pow_zero]⟩`.

Use the proof step `inv_mem' := by`. Introduce and unpack `a ⟨n, hn⟩`. Use `⟨n * (D.nd.l i ^ m - 1), ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv, hn]`. Use `symm`.

Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← pow_add, show n * (D.nd.l i ^ m - 1) + n = D.nd.l i ^ m * n by`. Rewrite using `[mul_comm n, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hL], pow_mul, hm, one_pow] }`. Establish `hker : (D.ntw.psiL i).ker ≤ H` using `fun x hx => ⟨0, by rw [pow_zero]; exact hx⟩`. Establish `hopen : IsOpen (H : Set (G D.host.E D.nd.Om))` using `Subgroup.isOpen_mono hker (D.ntw.psiL_open i)`.

Establish `hclosed : IsClosed (H : Set (G D.host.E D.nd.Om))` using `H.isClosed_of_isOpen hopen`. Establish `hgen : Subgroup.closure (insert (D.nd.gam0 i v) {σ : G D.host.E D.nd.Om | ∀ y : D.nd.Om, y ≠ 0 → (D.nd.plOm.1 v).valuation (σ y / y - 1) < 1}) ≤ H`. Rewrite using `[Subgroup.closure_le, Set.insert_subset_iff]`. Use `⟨⟨1, (pow_one _).symm⟩, fun σ hσ => ⟨0, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[pow_zero]`.

Conclude with `hW D.host.E D.nd.Om (D.nd.l i) Fact.out v (D.nd.plOm.1 v) (D.nd.plOm.2 v) hl (D.nd.O i)ˣ (D.ntw.psiL i) (D.ntw.psiL_open i) (D.ntw.psiL_ord i) σ hσ`. Establish `hT` using `(D.nd.restN_tameGenerator_generates i v (Or.inr hv)).2 hg`. Conclude with `closure_minimal hgen hclosed hT`.
-/
theorem qpow_of_tw (hW : WildTriv) (D : D7) (i : D.nd.Loc) :
    ∀ v ∈ D.nd.Q i, ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
      ∃ n : ℕ, D.nd.chi i 1 g = D.nd.chi i 1 (D.nd.gam0 i v) ^ n := by
  classical
  intro v hv g hg
  have hS : v ∉ D.nd.S i := fun h => Finset.disjoint_left.1 (D.nd.SQ_disj i) h hv
  have hl : v ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i v (Or.inr hv)
  have hgk : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := by
    intro k hk
    apply hS
    rw [D.nd.S_def i v]
    refine ⟨?_, hl⟩
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  have hpd : v ∉ D.ntw.pD (D.ntw.twOf i) := by
    intro hp
    have h' : v ∈ ((D.ntw.pD (D.ntw.twOf i) : Finset _) : Set (HeightOneSpectrum (𝓞 D.host.E))) := hp
    rw [D.ntw.pD_eq, D.ntw.twOf_l] at h'
    exact hS ((D.nd.S_def i v).2 ⟨Or.inr (Or.inr h'), hl⟩)
  have hl' : v ∉ placesOver D.host.E (D.ntw.l (D.ntw.twOf i)) := by
    rw [D.ntw.twOf_l]
    exact hl
  have hchi : ∀ h ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), D.nd.chi i 1 h = D.ntw.psiL i h := by
    intro h hh
    have h1 := D.ntw.twistCharacterFamily_unramified (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) v hl' hgk hpd (D.nd.plOm.1 v)
      (D.nd.plOm.2 v) h hh
    rw [D.ntw.chi_tw i, MonoidHom.mul_apply, MonoidHom.comp_apply, h1, map_one, one_mul]
  rw [hchi g hg, hchi _ (D.nd.locNd_chebotarevPlace_mem i v)]
  obtain ⟨m, hm⟩ := D.ntw.psiL_ord i (D.nd.gam0 i v)
  have hL : 1 ≤ D.nd.l i ^ m := Nat.one_le_pow _ _ (Fact.out : (D.nd.l i).Prime).pos
  let H : Subgroup (G D.host.E D.nd.Om) :=
    { carrier := {x | ∃ n : ℕ, D.ntw.psiL i x = D.ntw.psiL i (D.nd.gam0 i v) ^ n}
      mul_mem' := by
        rintro a b ⟨n, hn⟩ ⟨k, hk⟩
        exact ⟨n + k, by rw [map_mul, hn, hk, pow_add]⟩
      one_mem' := ⟨0, by rw [map_one, pow_zero]⟩
      inv_mem' := by
        rintro a ⟨n, hn⟩
        refine ⟨n * (D.nd.l i ^ m - 1), ?_⟩
        rw [map_inv, hn]
        symm
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_add, show n * (D.nd.l i ^ m - 1) + n = D.nd.l i ^ m * n by
          rw [mul_comm n, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hL], pow_mul, hm, one_pow] }
  have hker : (D.ntw.psiL i).ker ≤ H := fun x hx => ⟨0, by rw [pow_zero]; exact hx⟩
  have hopen : IsOpen (H : Set (G D.host.E D.nd.Om)) := Subgroup.isOpen_mono hker (D.ntw.psiL_open i)
  have hclosed : IsClosed (H : Set (G D.host.E D.nd.Om)) := H.isClosed_of_isOpen hopen
  have hgen : Subgroup.closure (insert (D.nd.gam0 i v) {σ : G D.host.E D.nd.Om | ∀ y : D.nd.Om, y ≠ 0 →
      (D.nd.plOm.1 v).valuation (σ y / y - 1) < 1}) ≤ H := by
    rw [Subgroup.closure_le, Set.insert_subset_iff]
    refine ⟨⟨1, (pow_one _).symm⟩, fun σ hσ => ⟨0, ?_⟩⟩
    rw [pow_zero]
    exact hW D.host.E D.nd.Om (D.nd.l i) Fact.out v (D.nd.plOm.1 v) (D.nd.plOm.2 v) hl (D.nd.O i)ˣ
      (D.ntw.psiL i) (D.ntw.psiL_open i) (D.ntw.psiL_ord i) σ hσ
  have hT := (D.nd.restN_tameGenerator_generates i v (Or.inr hv)).2 hg
  exact closure_minimal hgen hclosed hT

end Formalism.MainNotions.N

end
