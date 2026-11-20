import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.HSShort.SymCols

variable {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K A)

/- English proof (translation)
Simplify using `[word, List.ofFn_const, List.prod_replicate]`.
-/
theorem word_const (l : Fin N → K) (n : ℕ) : word mul (fun _ : Fin n => l) = mul l ^ n := by
  simp [word, List.ofFn_const, List.prod_replicate]

/- English proof (translation)
Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => funext k`. Simplify using `[join]`. Consider the case `cast i => funext k`. Simplify using `[join]`.
-/
theorem join_fun {D : ℕ} (s : Fin D → Fin N → K) (l : Fin N → K) (b : Fin (D + 1)) :
    (fun k => join s l (b, k)) = Fin.lastCases (motive := fun _ => Fin N → K) l s b := by
  induction b using Fin.lastCases with
  | last => funext k; simp [join]
  | cast i => funext k; simp [join]

/- English proof (translation)
Set `P` to `Submonoid.closure (Set.range mul)`. Use `letI : CommMonoid P := Submonoid.closureCommMonoidOfComm _ (by rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩; exact hc u v)`. Set `G : (Fin N → K) → P` to `fun u => ⟨mul u, Submonoid.subset_closure ⟨u, rfl⟩⟩`. Set `φ : P →* Module.End K A` to `P.subtype`. Establish `key : ∀ {n : ℕ} (f : Fin n → P), (List.ofFn fun i => φ (f i)).prod = φ (∏ i, f i)`.

Introduce `n f`. Rewrite using `[← List.prod_ofFn, map_list_prod, List.map_ofFn]`. Both sides reduce to the same expression. Set `H : Fin (D + 1) → Fin N → K` to `Fin.lastCases (motive := fun _ => Fin N → K) l s`. Establish `h1 : word mul (fun q k => join s l (β q, k)) = φ (∏ q, G (H (β q)))`.

Rewrite using `[← key]`. Simplify using `only [word, join_fun]`. Both sides reduce to the same expression. Establish `h2 : pw mul s α = φ (∏ i, G (s i) ^ α i)`. Rewrite using `[← key]`.

Simplify using `only [pw, map_pow]`. Both sides reduce to the same expression. Rewrite using `[h1, h2, show mul l ^ (Finset.univ.filter fun q => β q = Fin.last D).card = φ (G l ^ (Finset.univ.filter fun q => β q = Fin.last D).card) from (map_pow φ (G l) _).symm, ← map_mul]`. Use `congr 1`. Rewrite using `[Finset.prod_comp (fun b => G (H b)) β]`.

Rewrite using `[Finset.prod_subset (Finset.subset_univ _)]`. Rewrite using `[Fin.prod_univ_castSucc]`. Use `congr 1`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[H, hα]`.

Simplify using `[H]`. Introduce `b _ hb`. Establish `: (Finset.univ.filter fun q => β q = b).card = 0`. Rewrite using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Introduce `q _ hq`.

Conclude with `hb (Finset.mem_image.2 ⟨q, Finset.mem_univ _, hq⟩)`. Rewrite using `[this, pow_zero]`.
-/
theorem word_join (hc : ∀ u v, mul u * mul v = mul v * mul u) {D t : ℕ} (s : Fin D → Fin N → K) (l : Fin N → K)
    (β : Fin t → Fin (D + 1)) (α : Fin D →₀ ℕ)
    (hα : ∀ i : Fin D, (Finset.univ.filter fun q => β q = i.castSucc).card = α i) :
    word mul (fun q k => join s l (β q, k)) =
      pw mul s α * mul l ^ (Finset.univ.filter fun q => β q = Fin.last D).card := by
  classical
  let P := Submonoid.closure (Set.range mul)
  letI : CommMonoid P := Submonoid.closureCommMonoidOfComm _ (by rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩; exact hc u v)
  let G : (Fin N → K) → P := fun u => ⟨mul u, Submonoid.subset_closure ⟨u, rfl⟩⟩
  let φ : P →* Module.End K A := P.subtype
  have key : ∀ {n : ℕ} (f : Fin n → P), (List.ofFn fun i => φ (f i)).prod = φ (∏ i, f i) := by
    intro n f
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    rfl
  let H : Fin (D + 1) → Fin N → K := Fin.lastCases (motive := fun _ => Fin N → K) l s
  have h1 : word mul (fun q k => join s l (β q, k)) = φ (∏ q, G (H (β q))) := by
    rw [← key]
    simp only [word, join_fun]
    rfl
  have h2 : pw mul s α = φ (∏ i, G (s i) ^ α i) := by
    rw [← key]
    simp only [pw, map_pow]
    rfl
  rw [h1, h2, show mul l ^ (Finset.univ.filter fun q => β q = Fin.last D).card = φ (G l ^ (Finset.univ.filter fun q => β q = Fin.last D).card) from (map_pow φ (G l) _).symm, ← map_mul]
  congr 1
  rw [Finset.prod_comp (fun b => G (H b)) β]
  rw [Finset.prod_subset (Finset.subset_univ _)]
  · rw [Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [H, hα]
    · simp [H]
  · intro b _ hb
    have : (Finset.univ.filter fun q => β q = b).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro q _ hq
      exact hb (Finset.mem_image.2 ⟨q, Finset.mem_univ _, hq⟩)
    rw [this, pow_zero]

/- English proof (translation)
Use `Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := β) (fun _ _ => Finset.mem_univ _)` as an intermediate fact. Rewrite `this` using `[Finset.card_univ, Fintype.card_fin]`. Rewrite `this` using `[Fin.sum_univ_castSucc]`. Conclude with `this.symm`.
-/
theorem card_fibers {D t : ℕ} (β : Fin t → Fin (D + 1)) :
    ∑ i : Fin D, (Finset.univ.filter fun q => β q = i.castSucc).card +
      (Finset.univ.filter fun q => β q = Fin.last D).card = t := by
  classical
  have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := β)
    (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at this
  rw [Fin.sum_univ_castSucc] at this
  exact this.symm

end GlobalTheory.HSShort.SymCols

open GlobalTheory.HSShort.SymCols in
/- English proof (translation)
Introduce `F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d col m ix hsh l`. Use `⟨fun a α p => ?_, fun k hk hj => ?_⟩` and prove the remaining obligations. Use `set κ := col (ix (⟨a, α⟩, p)) with hκ`. Establish `hj : κ.j = 0` using `hsh.x_j _`. Establish `hx : (κ.x : A) = m p` using `hsh.x_vec _`.

Establish `htype : ∀ i : Fin S.D, (Finset.univ.filter fun q => κ.β q = i.castSucc).card = α.1 i` using `hsh.x_type _`. Establish `ht : κ.t = S.T` using `by have := κ.add; omega`. Establish `hdeg : ∑ i : Fin S.D, α.1 i = a` using `by rw [← Finsupp.degree_eq_sum]; exact α.2`. Establish `hlast : (Finset.univ.filter fun q => κ.β q = Fin.last S.D).card = S.T - a`. Use `card_fibers κ.β` as an intermediate fact.

Simplify using `only [htype, hdeg] at this`. Use linear arithmetic over natural numbers and integers. Establish `heq : word Φ.mul (fun q k => join s l (κ.β q, k)) (Φ.ι κ.x) = pw Φ.mul s α.1 (word Φ.mul (fun _ : Fin (S.T - a) => l) (Φ.ι (m p)))`. Rewrite using `[word_join Φ.mul Φ.comm s l κ.β α.1 htype, hlast, word_const, Module.End.mul_apply, hx]`. Take `⟨h, hsym⟩` from `Φ.mono a (by omega) α (fun _ => l) (Φ.ι (m p)) (Submodule.subset_span ⟨(m p : A), (m p).2, rfl⟩)`.

Rewrite using `[heq]`. Use `⟨h, fun α' p' => ?_⟩` and prove the remaining obligations. Rewrite using `[hsym]`. Simplify using the standard rewrite rules. Establish `hrest` using `hsh.rest k hk`.

Establish `hno : ∀ q, (col k).β q ≠ Fin.last S.D`. Break down `hrest with h | h` into its components or cases. Conclude with `h.2`. Use `hS.le_T` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Set `α : Fin S.D →₀ ℕ` to `Finsupp.equivFunOnFinite.symm (fun i => (Finset.univ.filter fun q => (col k).β q = i.castSucc).card)`. Establish `htype : ∀ i : Fin S.D, (Finset.univ.filter fun q => (col k).β q = i.castSucc).card = α i` using `fun i => rfl`. Establish `h0 : (Finset.univ.filter fun q => (col k).β q = Fin.last S.D).card = 0`. Rewrite using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Conclude with `fun q _ => hno q`.

Establish `ht : (col k).t = S.T - S.D` using `by have := (col k).add; omega`. Establish `hdeg : α.degree = S.T - S.D`. Rewrite using `[Finsupp.degree_eq_sum]`. Use `card_fibers (col k).β` as an intermediate fact. Rewrite `this` using `[h0]`.

Simplify `this` using `[α, ht]`. Rewrite using `[word_join Φ.mul Φ.comm s l (col k).β α htype, h0, pow_zero, mul_one, Φ.div]`. Use `Submodule.mem_iSup_of_mem ⟨α, hdeg⟩ (Submodule.mem_map_of_mem (Submodule.subset_span ⟨((col k).x : A), ?_, rfl⟩))` and prove the remaining obligations. Establish `key : ∀ (j : ℕ) (x : S.V j), j = S.D → (x : A) ∈ S.V S.D` using `by rintro j x rfl; exact x.2`. Conclude with `key _ _ hj`.
-/
theorem GlobalTheory.HSShort.symbols_of_columns : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (col : Fin d → S.Col) (m : Fin δ → S.V 0) (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d), S.Shape δ col m ix → ∀ l : Fin S.N → E, (∀ (a : Fin (S.T - S.D)) (α : MonoDeg (Fin S.D) a) (p : Fin δ), ∃ h : word Φ.mul (fun q k => join s l ((col (ix (⟨a, α⟩, p))).β q, k)) (Φ.ι (col (ix (⟨a, α⟩, p))).x) ∈ Φ.U a, ∀ α' p', Φ.sym a ⟨_, h⟩ (α', p') = if α'.1 = α.1 then (∑ k, l k * Φ.y p' k) ^ (S.T - a) * Φ.res (Φ.ι (m p)) p' else 0) ∧ ∀ k, k ∉ Set.range ix → (col k).j = S.D → word Φ.mul (fun q j => join s l ((col k).β q, j)) (Φ.ι (col k).x) ∈ Φ.U (S.T - S.D) := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d col m ix hsh l
  refine ⟨fun a α p => ?_, fun k hk hj => ?_⟩
  · set κ := col (ix (⟨a, α⟩, p)) with hκ
    have hj : κ.j = 0 := hsh.x_j _
    have hx : (κ.x : A) = m p := hsh.x_vec _
    have htype : ∀ i : Fin S.D, (Finset.univ.filter fun q => κ.β q = i.castSucc).card = α.1 i := hsh.x_type _
    have ht : κ.t = S.T := by have := κ.add; omega
    have hdeg : ∑ i : Fin S.D, α.1 i = a := by rw [← Finsupp.degree_eq_sum]; exact α.2
    have hlast : (Finset.univ.filter fun q => κ.β q = Fin.last S.D).card = S.T - a := by
      have := card_fibers κ.β
      simp only [htype, hdeg] at this
      omega
    have heq : word Φ.mul (fun q k => join s l (κ.β q, k)) (Φ.ι κ.x) =
        pw Φ.mul s α.1 (word Φ.mul (fun _ : Fin (S.T - a) => l) (Φ.ι (m p))) := by
      rw [word_join Φ.mul Φ.comm s l κ.β α.1 htype, hlast, word_const, Module.End.mul_apply, hx]
    obtain ⟨h, hsym⟩ := Φ.mono a (by omega) α (fun _ => l) (Φ.ι (m p))
      (Submodule.subset_span ⟨(m p : A), (m p).2, rfl⟩)
    rw [heq]
    refine ⟨h, fun α' p' => ?_⟩
    rw [hsym]
    simp
  · have hrest := hsh.rest k hk
    have hno : ∀ q, (col k).β q ≠ Fin.last S.D := by
      rcases hrest with h | h
      · exact h.2
      · have := hS.le_T; omega
    classical
    let α : Fin S.D →₀ ℕ := Finsupp.equivFunOnFinite.symm
      (fun i => (Finset.univ.filter fun q => (col k).β q = i.castSucc).card)
    have htype : ∀ i : Fin S.D, (Finset.univ.filter fun q => (col k).β q = i.castSucc).card = α i := fun i => rfl
    have h0 : (Finset.univ.filter fun q => (col k).β q = Fin.last S.D).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun q _ => hno q
    have ht : (col k).t = S.T - S.D := by have := (col k).add; omega
    have hdeg : α.degree = S.T - S.D := by
      rw [Finsupp.degree_eq_sum]
      have := card_fibers (col k).β
      rw [h0] at this
      simpa [α, ht] using this
    rw [word_join Φ.mul Φ.comm s l (col k).β α htype, h0, pow_zero, mul_one, Φ.div]
    refine Submodule.mem_iSup_of_mem ⟨α, hdeg⟩ (Submodule.mem_map_of_mem (Submodule.subset_span ⟨((col k).x : A), ?_, rfl⟩))
    have key : ∀ (j : ℕ) (x : S.V j), j = S.D → (x : A) ∈ S.V S.D := by rintro j x rfl; exact x.2
    exact key _ _ hj
