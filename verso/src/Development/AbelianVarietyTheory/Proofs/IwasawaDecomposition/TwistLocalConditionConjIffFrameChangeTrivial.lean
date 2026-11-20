import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalCondMoveDecoratedLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDeterminantEqNormOneClassOfLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

variable {B : Base} {X : PreX B.toPre}

/- English proof (translation)
Use `congrArg (fun g : GL (Fin n) (TensorProduct (↥B.host.F) B.host.E (HeightOneSpectrum.adicCompletion (↥B.host.F) v)) => (g.1 : Matrix (Fin n) (Fin n) _) r j) h` as an intermediate fact. Simplify `this` using `[bc, Matrix.one_apply]`.
-/
theorem bc_prV_entry {B : Base} (v : HeightOneSpectrum (𝓞 B.host.F)) {n : ℕ} (m : GA B n)
    (h : bc (prV (E := B.host.E) v) m = 1) (r j : Fin n) :
    prV (E := B.host.E) v ((m : Matrix (Fin n) (Fin n) _) r j) = if r = j then 1 else 0 := by
  have := congrArg (fun g : GL (Fin n) (TensorProduct (↥B.host.F) B.host.E (HeightOneSpectrum.adicCompletion (↥B.host.F) v)) =>
    (g.1 : Matrix (Fin n) (Fin n) _) r j) h
  simpa [bc, Matrix.one_apply] using this

/- English proof (translation)
Introduce `hmem`. Establish `h0 : ((g : 𝓞 F ⧸ w.asIdeal)) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hmem`. Establish `hdvd : ringChar (𝓞 F ⧸ w.asIdeal) ∣ g` using `ringChar.dvd h0`.

Use `haveI : Nontrivial (𝓞 F ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top`. Establish `hne : ringChar (𝓞 F ⧸ w.asIdeal) ≠ 1` using `CharP.ringChar_ne_one`. Break down `(Nat.dvd_prime hg).1 hdvd with h | h` into its components or cases. Conclude with `hne h`. Apply `hw.2.2 show ringChar (𝓞 F ⧸ w.asIdeal) ∈ S` to reduce the goal to its premises.

Rewrite using `[h]`. Conclude with `hgS`.
-/
theorem natCast_not_mem_of_goodPl {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [Algebra F E]
    {S : Set ℕ} {w : HeightOneSpectrum (𝓞 F)} (hw : GoodPl E S w) {g : ℕ} (hg : Nat.Prime g) (hgS : g ∈ S) :
    ((g : 𝓞 F) ∉ w.asIdeal) := by
  intro hmem
  have h0 : ((g : 𝓞 F ⧸ w.asIdeal)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hmem
  have hdvd : ringChar (𝓞 F ⧸ w.asIdeal) ∣ g := ringChar.dvd h0
  haveI : Nontrivial (𝓞 F ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  have hne : ringChar (𝓞 F ⧸ w.asIdeal) ≠ 1 := CharP.ringChar_ne_one
  rcases (Nat.dvd_prime hg).1 hdvd with h | h
  · exact hne h
  · apply hw.2.2
    show ringChar (𝓞 F ⧸ w.asIdeal) ∈ S
    rw [h]; exact hgS

/- English proof (translation)
Introduce `B X I hI l u a Q hQ n t s θ ht hs`. Establish `key : ∀ (P : I.Q a) (r j : Fin n), adAt B.host.F P.1 (((t⁻¹ * s * t : GA B n) : Matrix (Fin n) (Fin n) _) r j) = if r = j then 1 else 0`. Introduce `P r j`. Establish `hvQ : HeightOneSpectrum.under (𝓞 B.host.F) P.1 ∈ Q` using `(hQ _).2 ⟨P.1, P.2, rfl⟩`. Take `⟨w, -, hsel, hgood⟩` from `ColIn.exists_of_mem_Q I P.2`.

Establish `hvw : HeightOneSpectrum.under (𝓞 B.host.F) P.1 = w` using `by ext1`. Use `hI.sel_ok w` as an intermediate fact. Rewrite `this` using `[hsel]`. Conclude with `this`. Establish `htv : bc (prV (E` using `B.host.E) w) t = 1 := ht w (Or.inr fun j => natCast_not_mem_of_goodPl B.fields.E hgood (B.host.g_prime j) (hI.g_mem j))`.

Establish `hsv : bc (prV (E` using `B.host.E) w) s = 1 := hs w (hvw ▸ hvQ)`. Establish `hm : bc (prV (E` using `B.host.E) w) (t⁻¹ * s * t) = 1 := by`. Rewrite using `[MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv, htv, hsv, inv_one, one_mul, one_mul]`. Apply the tactic sequence `have entry := bc_prV_entry w _ hm r j`. Use `split_ifs with hrj`.

Conclude with `GlobalTheory.Mem.Col2.FullDt.adAt_eq_one_of_prV P.1 (by rw [hvw, entry, if_pos hrj])`. Conclude with `GlobalTheory.Mem.Col2.TilX.adAt_eq_zero_of_prV P.1 _ (by rw [hvw, entry, if_neg hrj])`. Prove the components needed by the constructor for the conclusion. Introduce `hL`. Use function extensionality and compare the values at `P`.

Use `show θ P = 1`. Rewrite using `[← inv_eq_one]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `(Pi.basisFun B.fields.E (Fin n)).ext'` to reduce the goal to its premises. Introduce `j`.

Use function extensionality and compare the values at `r`. Establish `h1` using `hL P r j`. Rewrite `h1` using `[key P r j]`. Establish `h2 : algebraMap B.host.E (HeightOneSpectrum.adicCompletion B.host.E P.1) ((((θ P)⁻¹ : ↥(GLint B.fields.E n P.1)).1) (Pi.single j 1) r) = algebraMap B.host.E _ ((Pi.single j (1 : B.host.E) : Fin n → B.host.E) r)`. Apply the tactic sequence `rw [← h1, Pi.single_apply]; split_ifs <;> simp`.

Establish `h3` using `(algebraMap B.host.E (HeightOneSpectrum.adicCompletion B.host.E P.1)).injective h2`. Simplify `h3` using `[Pi.basisFun_apply]`. Introduce and unpack `rfl`. Introduce `P r j`. Rewrite using `[key P r j]`.

Simplify using `[Pi.single_apply]`.
-/
theorem locCQ_conj_iff_eq_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι)
    (Q : Finset (HeightOneSpectrum (𝓞 B.host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → ∀ (n : ℕ) (t s : GA B n) (θ : GLQ B.fields.E n (I.Q a)),
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) →
      bc (prV (E := B.host.E) v) t = 1) →
    (∀ v ∈ Q, bc (prV (E := B.host.E) v) s = 1) →
    (LocCQ (I.Q a) n (t⁻¹ * s * t) θ ↔ θ = 1) := by
  intro B X I hI l u a Q hQ n t s θ ht hs
  have key : ∀ (P : I.Q a) (r j : Fin n),
      adAt B.host.F P.1 (((t⁻¹ * s * t : GA B n) : Matrix (Fin n) (Fin n) _) r j) = if r = j then 1 else 0 := by
    intro P r j
    have hvQ : HeightOneSpectrum.under (𝓞 B.host.F) P.1 ∈ Q := (hQ _).2 ⟨P.1, P.2, rfl⟩
    obtain ⟨w, -, hsel, hgood⟩ := ColIn.exists_of_mem_Q I P.2
    have hvw : HeightOneSpectrum.under (𝓞 B.host.F) P.1 = w := by
      ext1
      have := hI.sel_ok w
      rw [hsel] at this
      exact this
    have htv : bc (prV (E := B.host.E) w) t = 1 :=
      ht w (Or.inr fun j => natCast_not_mem_of_goodPl B.fields.E hgood (B.host.g_prime j) (hI.g_mem j))
    have hsv : bc (prV (E := B.host.E) w) s = 1 := hs w (hvw ▸ hvQ)
    have hm : bc (prV (E := B.host.E) w) (t⁻¹ * s * t) = 1 := by
      rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv, htv, hsv, inv_one, one_mul, one_mul]
    have entry := bc_prV_entry w _ hm r j
    split_ifs with hrj
    · exact GlobalTheory.Mem.Col2.FullDt.adAt_eq_one_of_prV P.1 (by rw [hvw, entry, if_pos hrj])
    · exact GlobalTheory.Mem.Col2.TilX.adAt_eq_zero_of_prV P.1 _ (by rw [hvw, entry, if_neg hrj])
  constructor
  · intro hL
    funext P
    show θ P = 1
    rw [← inv_eq_one]
    apply Subtype.ext
    apply (Pi.basisFun B.fields.E (Fin n)).ext'
    intro j
    funext r
    have h1 := hL P r j
    rw [key P r j] at h1
    have h2 : algebraMap B.host.E (HeightOneSpectrum.adicCompletion B.host.E P.1)
        ((((θ P)⁻¹ : ↥(GLint B.fields.E n P.1)).1) (Pi.single j 1) r) =
        algebraMap B.host.E _ ((Pi.single j (1 : B.host.E) : Fin n → B.host.E) r) := by
      rw [← h1, Pi.single_apply]; split_ifs <;> simp
    have h3 := (algebraMap B.host.E (HeightOneSpectrum.adicCompletion B.host.E P.1)).injective h2
    simpa [Pi.basisFun_apply] using h3
  · rintro rfl
    intro P r j
    rw [key P r j]
    simp [Pi.single_apply]

end GlobalTheory.Mem.Col2.TC.ChTw.Match
