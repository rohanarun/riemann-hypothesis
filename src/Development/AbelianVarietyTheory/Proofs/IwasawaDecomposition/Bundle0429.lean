module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.BlockTheory.RationalLaws.RationalAdjointLaw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupActsByLiftTranslationPrincipalType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OfBeforeProjector
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapTypingsEquiv
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapRefCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open _root_.Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeDeterminantCharacters
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem evR_one {S : Type} [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) : evR Xo c 1 y = 1 :=
  evalAt_one _ _ y (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c S y)

theorem evR_smul {S : Type} [CommRing S] [Algebra c.F S] (a : c.F) (f : Rul Xo c) (y : FrPt Xo c S) :
    evR Xo c (a • f) y = algebraMap c.F S a * evR Xo c f y := evalAt_smul _ _ a f y

theorem trace_value {K L : Type} [Field K] [CharZero K] [Field L] [Algebra K L] [Module.Finite K L] [Algebra K ℂ] (x : L) (c0 : ℂ)
    (h : ∀ j : L →ₐ[K] ℂ, j x = c0) : ∃ u : K, algebraMap K ℂ u = c0 := by
  have h1 := trace_eq_sum_embeddings ℂ (K := K) (L := L) (x := x)
  simp only [h, Finset.sum_const, Finset.card_univ, AlgHom.card, nsmul_eq_mul] at h1
  have h2 : (Module.finrank K L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  exact ⟨Algebra.trace K L x / Module.finrank K L, by rw [map_div₀, h1, map_natCast]; field_simp⟩

theorem eq_const_of_complex (σ : c.F →+* ℂ) {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) (c0 : ℂ)
    (h : ∀ y : FrPt Xo c (CAt σ), toC (evR Xo c f y) = c0) (y : FrPt Xo c (CAt σ)) :
    ∃ u : c.F, σ u = c0 ∧ f = u • 1 := by
  have hB := GlobalTheory.firstFiveLaws.1.secBaseChange
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  haveI : Nontrivial (CAt σ) := inferInstanceAs (Nontrivial ℂ)
  obtain ⟨p, φ, y₀, -⟩ := GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c _ y
  obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal (RingHom.ker φ.toRingHom) (RingHom.ker_ne_top _)
  letI : Algebra c.F ℂ := σ.toAlgebra
  letI := Ideal.Quotient.field m
  haveI : Module.Finite c.F (p.R ⧸ m) := finite_of_finite_type_of_isJacobsonRing c.F _
  obtain ⟨u, hu⟩ := trace_value (K := c.F) (Ideal.Quotient.mk m (f p y₀)) c0 fun j => by
    let ψ : p.R →ₐ[c.F] CAt σ := (j.comp (Ideal.Quotient.mkₐ c.F m) : p.R →ₐ[c.F] ℂ)
    obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c _ _ ψ y₀
    exact (GlobalTheory.ShortSpanCompare.evR_of_frMap hf ψ hz).symm.trans (h z)
  refine ⟨u, hu, GlobalTheory.CoverPinCompare.eq_of_complex σ hf
    (Submodule.smul_mem _ u (GlobalTheory.LevelCover.one_mem_sec_zero _ _)) fun z => ?_⟩
  rw [evR_smul, evR_one, mul_one]
  exact (h z).trans hu.symm

variable {Cl : Type} [Fintype Cl] {Vs : Type} [AddCommGroup Vs] [Module c.F Vs]

end Cover

section Core

variable {D : D7}

variable (T : CoreJ D) (i : Fin D.R.m) {c' : Coeff T.Q.l} (hle : T.Q.c.F ≤ c'.F)
  (hV : T.V ((i : ℕ) + 1) (sigB T hle) = Wc D i)


end Core

section Clauses

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  (O : OMDat T.toCore R i Unit fun _ => A.μ0) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)


set_option maxHeartbeats 1000000 in
theorem cover_const (hT : LawsJ T) (hL : R.toLevCh.Is A.μ0)
    (hP : O.Pins κ v₀ (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) :
    ∃ u : O.c'.F, (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ (O.dδ ()).cδ = (O.dδ ()).eF u • 1 := by
  have hj := GlobalTheory.LevelEquivCompare.inR i
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by
    have := (GlobalTheory.Member.exists_iotaOK D T.Q hT.pins _ hj).2
    omega
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT _ hj O.s0 rfl (Wc D i) O.hV (rank_Wc i)
  obtain ⟨c0, ⟨m, hm, hc⟩, H⟩ := hP.cxi
  obtain ⟨hU, hW, g, e, F, ik, φ, th, hth, hdl, hval⟩ := H ()
  have hv : ∀ h, rdU (O.U₂ ()) (O.dδ ()).cδ (O.dict₂ () h).1 (O.dict₂ () h).2 = c0 := fun h => by
    obtain ⟨γ, h1, h2, h3, -⟩ := hdl.2 h
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D i)).1 (γ * h)
    rw [hval h γ ⟨h1, h2, h3⟩, (hP.tuple ()).xi _ x hx,
      GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0) x, Circle.coe_one, mul_one]
  have hs := (hP.cov ()).1.2.2.2.2.2.2.2.1
  have hd : (O.dict₂ () 1).2 ∈ ((O.U₂ ()).X (O.dict₂ () 1).1).dom := by
    by_contra hd
    have h0 : c0 = 0 := (hv 1).symm.trans (dif_neg hd)
    rw [h0, zero_pow hm.ne'] at hc
    exact zero_ne_one hc
  obtain ⟨u, hu, hf⟩ := eq_const_of_complex _ hs c0 (GlobalTheory.Member.const_of_const_on_dictLat D _ _ _ _ _ _ _ _ _ (O.U₂ ()) (O.dict₂ ()) _ g e F ik φ th _
    hio hpos (hP.cov ()).2.1 rfl hx₀ hU hW hth hdl _ hs c0 hv) ((O.U₂ ()).un _ ⟨_, hd⟩)
  refine ⟨(O.dδ ()).eF.symm u, ⟨m, hm, (inC O.c').injective ?_⟩, by rw [AlgEquiv.apply_symm_apply]; exact hf⟩
  rw [map_pow, map_one]
  exact (congrArg (· ^ m) hu).trans hc

variable (cc : Cmp T i O.hle → ℂ)

variable (h : O.Cl' () → GA D (Vc D i))



end Clauses

section Rows

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  (O : OMDat T.toCore R i Unit fun _ => A.μ0) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)
  (h : O.Cl' () → GA D (Vc D i))



end Rows

section Back

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  {c' : Coeff T.Q.l} (hle : T.Q.c.F ≤ c'.F) (hV : T.V ((i : ℕ) + 1) (sigB T hle) = Wc D i) (jL : D.what₂.LL →+* c'.F)
  (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) ×
    ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La))
  (c0' : VsV D i c'.F →ₛₗ[c'.F.val.toRingHom] (R.cV i).W)
  (io : VsV D i c'.F →ₗ[c'.F] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c'.F)
  (dδ : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank) {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i))
  (La : Cl → GenLat D.host.E (Vc D i).rank) (Nc gam : Cl → ℕ) (vol : c'.F) (ep : Cl → c'.F)
  (w : Cl → (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) dδ.l₂) → c'.F) (v₀ : (R.MW i (sg0 D A)).Vec)

variable (κ : WeightFamilies.Wt D ((i : ℕ) + 1))



end Back

section Closed

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (i : Fin D.R.m)




end Closed

end GlobalTheory.OneMapRefCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistLocalConditionConjIffFrameChangeTrivial
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

variable {B : Base} {X : PreX B.toPre}

theorem bc_prV_entry {B : Base} (v : HeightOneSpectrum (𝓞 B.host.F)) {n : ℕ} (m : GA B n)
    (h : bc (prV (E := B.host.E) v) m = 1) (r j : Fin n) :
    prV (E := B.host.E) v ((m : Matrix (Fin n) (Fin n) _) r j) = if r = j then 1 else 0 := by
  have := congrArg (fun g : GL (Fin n) (TensorProduct (↥B.host.F) B.host.E (HeightOneSpectrum.adicCompletion (↥B.host.F) v)) =>
    (g.1 : Matrix (Fin n) (Fin n) _) r j) h
  simpa [bc, Matrix.one_apply] using this

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
end
end

