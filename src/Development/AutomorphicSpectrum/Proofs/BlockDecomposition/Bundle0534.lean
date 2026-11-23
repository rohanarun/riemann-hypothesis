module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0041
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0514
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
public import GroundTheory.LocalFields.Bundle0016
public import GroundTheory.LocalFields.KroneckerWeber
public import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0517
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0476
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0492
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0516
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0525
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0381
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0506
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemHROfGram
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WittS

section Abstract

variable {A B : Type} [CommRing A] [CommRing B]

theorem map_mul_of_mul (Q : B →+ A) (hQ : ∀ y y', Q (y * y') = Q y * Q y')
    {a b c : Type} [Fintype b] (X : Matrix a b B) (Y : Matrix b c B) :
    (X * Y).map Q = X.map Q * Y.map Q := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mul_apply, map_sum, hQ]

theorem exists_lift {m : Type} [Fintype m] [DecidableEq m] (c : A →+* A) (s : B →+* B) (P : A →+* B)
    (Q : B →+ A) (e : A) (hQs : ∀ y, Q (s y) = c (Q y)) (hQP : ∀ x, Q (P x) = e * x)
    (hQ : ∀ y y', Q (y * y') = Q y * Q y') (J : Matrix m m A) (g g' : Matrix m m B)
    (hgg' : g * g' = 1) (hg'g : g' * g = 1) (hU : (g.map s)ᵀ * J.map P * g = J.map P) :
    ∃ h h' : Matrix m m A, h * h' = 1 ∧ h' * h = 1 ∧ (h.map c)ᵀ * J * h = J ∧
      e • (h - 1) = h - 1 ∧
      ∀ (ι : Type) (N N' : Matrix m ι A), e • N = N → e • N' = N' → g * N.map P = N'.map P →
        h * N = N' := by
  have hQ1 : Q 1 = e := by simpa using hQP 1
  have hQe : ∀ y, e * Q y = Q y := fun y => by rw [← hQ1, ← hQ, one_mul]
  have hee : e * e = e := by simpa [hQ1] using hQe 1
  have hce : c e = e := by rw [← hQ1, ← hQs, map_one]
  have hGe : ∀ {a b : Type} (X : Matrix a b B), e • X.map Q = X.map Q := by
    intro a b X
    ext i j
    simp [hQe]
  have hfz : ∀ {a b : Type} (X : Matrix a b B), (1 - e) • X.map Q = 0 := by
    intro a b X
    rw [sub_smul, one_smul, hGe, sub_self]
  have h1Q : (1 : Matrix m m B).map Q = e • 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hQ1]
    · simp [Matrix.one_apply_ne hij]
  have hPQ : ∀ {a b : Type} (X : Matrix a b A), (X.map P).map Q = e • X := by
    intro a b X
    ext i j
    simp [hQP]
  have hfe : (1 - e) * (1 - e) = 1 - e := by linear_combination hee
  have hef : e * (1 - e) = 0 := by linear_combination -hee
  have hsum : ∀ {a b : Type} (X : Matrix a b A), e • X + (1 - e) • X = X := by
    intro a b X
    rw [← add_smul]
    simp
  have hmul : ∀ {a b c : Type} [Fintype b] (X : Matrix a b B) (Y : Matrix b c B),
      (X * Y).map Q = X.map Q * Y.map Q := fun X Y => map_mul_of_mul Q hQ X Y
  have hinv : ∀ u v : Matrix m m B, u * v = 1 →
      (u.map Q + (1 - e) • 1) * (v.map Q + (1 - e) • 1) = 1 := by
    intro u v huv
    rw [add_mul, mul_add, mul_add, ← hmul, huv, h1Q]
    simp only [smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hfz, smul_smul, hfe, add_zero,
      zero_add]
    exact hsum 1
  have hstar : ((g.map Q + (1 - e) • (1 : Matrix m m A)).map c)ᵀ =
      ((g.map s)ᵀ).map Q + (1 - e) • 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hQs, hce]
    · simp [hQs, hce, Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
  refine ⟨g.map Q + (1 - e) • 1, g'.map Q + (1 - e) • 1, hinv _ _ hgg', hinv _ _ hg'g, ?_, ?_, ?_⟩
  · rw [hstar]
    have hJ : ((g.map s)ᵀ).map Q * J * g.map Q = e • J := by
      have h0 : ((g.map s)ᵀ).map Q * (e • J) = ((g.map s)ᵀ).map Q * J := by
        rw [mul_smul_comm, ← smul_mul_assoc, hGe]
      rw [← h0, ← hPQ J, ← hmul, ← hmul, hU]
    have hL : (1 - e) • (((g.map s)ᵀ).map Q * J) = 0 := by
      rw [← smul_mul_assoc, hfz, zero_mul]
    have hR : (1 - e) • (J * g.map Q) = 0 := by
      rw [← mul_smul_comm, hfz, mul_zero]
    simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hJ, hL, hR,
      smul_smul, hfe, add_zero, zero_add]
    exact hsum J
  · have h1 : g.map Q + (1 - e) • (1 : Matrix m m A) - 1 = g.map Q - e • 1 := by
      rw [sub_smul, one_smul]
      abel
    rw [h1, smul_sub, hGe, smul_smul, hee]
  · intro ι N N' hN hN' hg
    have hz : (1 - e) • N = 0 := by
      rw [sub_smul, one_smul, hN, sub_self]
    rw [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hz, add_zero]
    have h2 : g.map Q * N = g.map Q * (e • N) := by rw [hN]
    rw [h2, ← hPQ N, ← hmul, hg, hPQ, hN']

end Abstract

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_mem_HR_of_gram (σ : E →ₐ[F] E) (hCM : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J)
    (Ad : Type) [CommRing Ad] [Algebra F Ad] (R : Type) [CommRing R] [Algebra F R]
    [IsArtinianRing R] [IsReduced R] (e : Ad ⊗[F] E)
    (P : Ad ⊗[F] E →+* R ⊗[F] E) (Q : R ⊗[F] E →+ Ad ⊗[F] E)
    (hPinc : ∀ x, P (inclR Ad x) = inclR R x)
    (hPc : ∀ x, P (sigR Ad σ x) = sigR R σ (P x))
    (hQs : ∀ y, Q (sigR R σ y) = sigR Ad σ (Q y)) (hPQ : ∀ y, P (Q y) = y)
    (hQP : ∀ x, Q (P x) = e * x) (hQm : ∀ y y', Q (y * y') = Q y * Q y')
    (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι E) (hΓ : Γ.det ≠ 0)
    (N N' : Matrix (Fin M) ι (Ad ⊗[F] E)) (hN : e • N = N) (hN' : e • N' = N')
    (hG : (HMul.hMul (N.map (sigR Ad σ))ᵀ (HMul.hMul (J.map (inclR Ad) : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N : Matrix (Fin M) ι (Ad ⊗[F] E)) : Matrix ι ι (Ad ⊗[F] E)) = e • Γ.map (inclR Ad))
    (hG' : (HMul.hMul (N'.map (sigR Ad σ))ᵀ (HMul.hMul (J.map (inclR Ad) : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N' : Matrix (Fin M) ι (Ad ⊗[F] E)) : Matrix ι ι (Ad ⊗[F] E)) = e • Γ.map (inclR Ad)) :
    ∃ h : HR Ad σ J, e • ((h.1 : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) - 1) =
        (h.1 : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) - 1 ∧
      (HMul.hMul (h.1 : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N : Matrix (Fin M) ι (Ad ⊗[F] E)) = N' := by
  have hQ1 : Q 1 = e := by simpa using hQP 1
  have hPe : P e = 1 := by rw [← hQ1, hPQ]
  let eqv := Fintype.equivFin ι
  have gramX : ∀ N₀ : Matrix (Fin M) ι (Ad ⊗[F] E),
      (HMul.hMul (N₀.map (sigR Ad σ))ᵀ (HMul.hMul (J.map (inclR Ad) : Matrix (Fin M) (Fin M) (Ad ⊗[F] E)) N₀ : Matrix (Fin M) ι (Ad ⊗[F] E)) : Matrix ι ι (Ad ⊗[F] E)) = e • Γ.map (inclR Ad) →
      gramR R σ J (fun a i => P (N₀ i (eqv.symm a))) =
        (Γ.submatrix eqv.symm eqv.symm).map (inclR R) := by
    intro N₀ h₀
    ext a b
    have h := congrArg (fun X : Matrix ι ι (Ad ⊗[F] E) => P (X (eqv.symm a) (eqv.symm b))) h₀
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
      smul_eq_mul, map_sum, map_mul, hPc, hPe, one_mul, hPinc, Finset.mul_sum] at h
    simp only [gramR, hR, Formalism.UG.hform, JR, Matrix.map_apply, Matrix.submatrix_apply, mul_assoc]
    exact h
  have hXY := (gramX N hG).trans (gramX N' hG').symm
  have hdet : IsUnit (gramR R σ J (fun a i => P (N i (eqv.symm a)))).det := by
    rw [gramX N hG, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_submatrix_equiv_self]
    exact (isUnit_iff_ne_zero.mpr hΓ).map _
  obtain ⟨hU, hact⟩ := GlobalTheory.CompanionTheory.SW.WittTuples.exists_actW_eq_of_gramR_eq F E σ hCM M J hJ R _ _ _
    hXY hdet
  let g : GL (Fin M) (R ⊗[F] E) := HeckeCharacterZeroLocus.SiegelWeilU.HA.mat R σ J hU
  have hJP : (J.map (inclR Ad)).map P = J.map (inclR R) := by
    ext i j
    simp [hPinc]
  have hmem : ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map (sigR R σ))ᵀ *
      (J.map (inclR Ad)).map P * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      (J.map (inclR Ad)).map P := by
    rw [hJP]
    let h' : HeckeCharacterZeroLocus.SiegelWeilU.HR R σ J := hU
    exact h'.2
  have hgN : (HMul.hMul (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (N.map P) : Matrix (Fin M) ι (R ⊗[F] E)) = N'.map P := by
    ext i k
    have := congrFun (congrFun hact (eqv k)) i
    simpa [GlobalTheory.CompanionTheory.SW.actW, HeckeCharacterZeroLocus.SiegelWeilU.actTup, Matrix.mulVec, dotProduct, Matrix.mul_apply, g]
      using this
  obtain ⟨h, h', h1, h2, h3, h4, h5⟩ := exists_lift (sigR Ad σ) (sigR R σ) P Q e hQs hQP hQm
    (J.map (inclR Ad)) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))
    ((g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (by simp) (by simp) hmem
  let u : GL (Fin M) (Ad ⊗[F] E) := ⟨h, h', h1, h2⟩
  have hu : u ∈ HR Ad σ J := h3
  exact ⟨⟨u, hu⟩, h4, h5 ι N N' hN hN' hgN⟩

end General

theorem exists_unitary_off_S : (∀ (D : D7) (S : Finset (Pl D)) (e : AE D), IsIdem S e → ∃ (R : Type) (_ : CommRing R) (_ : Algebra D.host.F R) (_ : IsArtinianRing R) (_ : IsReduced R) (P : AE D →+* R ⊗[D.host.F] D.host.E) (Q : R ⊗[D.host.F] D.host.E →+ AE D), (∀ x, P (incA D x) = inclR R x) ∧ (∀ x, P (cA D x) = sigR R D.sp.cm.sig (P x)) ∧ (∀ y, Q (sigR R D.sp.cm.sig y) = cA D (Q y)) ∧ (∀ y, P (Q y) = y) ∧ (∀ x, Q (P x) = e * x) ∧ ∀ y y', Q (y * y') = Q y * Q y') → ∀ (D : D7) (V : HSp D) (S : Finset (Pl D)) (e : AE D), IsIdem S e → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι D.host.E), Γ.det ≠ 0 → ∀ N N' : Matrix (Fin V.rank) ι (AE D), e • N = N → e • N' = N' → (HMul.hMul (N.map (cA D))ᵀ (HMul.hMul (gA V) N : Matrix (Fin V.rank) ι (AE D)) : Matrix ι ι (AE D)) = e • Γ.map (incA D) → (HMul.hMul (N'.map (cA D))ᵀ (HMul.hMul (gA V) N' : Matrix (Fin V.rank) ι (AE D)) : Matrix ι ι (AE D)) = e • Γ.map (incA D) → ∃ h : GA D V, e • (mt V h - 1) = mt V h - 1 ∧ (HMul.hMul (mt V h) N : Matrix (Fin V.rank) ι (AE D)) = N' := by
  intro H D V S e he ι _ _ Γ hΓ N N' hN hN' hG hG'
  obtain ⟨R, _, _, _, _, P, Q, hPinc, hPc, hQs, hPQ, hQP, hQm⟩ := H D S e he
  obtain ⟨h, h1, h2⟩ := exists_mem_HR_of_gram D.sp.cm.sig (isCMExt_host D) V.gram (isHermND_gram V)
    (AF D.host.F) R e P Q hPinc hPc hQs hPQ hQP hQm ι Γ hΓ N N' hN hN' hG hG'
  exact ⟨h, h1, h2⟩

end GlobalTheory.CompanionTheory.WittS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegativeSchwartzBump
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicBump

open NumberField IsDedekindDomain _root_.Topology
open scoped Classical

theorem exists_compact_open_nhds (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {w₀ : κ → FiniteAdeleRing (𝓞 F) F} {B : Set (κ → FiniteAdeleRing (𝓞 F) F)} (hB : B ∈ 𝓝 w₀) :
    ∃ C : Set (κ → FiniteAdeleRing (𝓞 F) F), IsOpen C ∧ IsCompact C ∧ IsClosed C ∧ w₀ ∈ C ∧ C ⊆ B := by
  rw [nhds_pi, Filter.mem_pi] at hB
  obtain ⟨I, -, t, ht, hsub⟩ := hB
  have hO : (⋂ i, (fun a => w₀ i + a) ⁻¹' t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) :=
    Filter.iInter_mem.mpr fun i =>
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using ht i)
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hO
  have hNF : ((N : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  let c : FiniteAdeleRing (𝓞 F) F := algebraMap F _ ((N : F)⁻¹)
  have hcN : (N : FiniteAdeleRing (𝓞 F) F) * c = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul, mul_inv_cancel₀ hNF, map_one]
  have hNc : c * (N : FiniteAdeleRing (𝓞 F) F) = 1 := by rw [mul_comm]; exact hcN
  let h : FiniteAdeleRing (𝓞 F) F ≃ₜ FiniteAdeleRing (𝓞 F) F :=
    { toFun := fun u => c * u
      invFun := fun u => (N : FiniteAdeleRing (𝓞 F) F) * u
      left_inv := fun u => by
        show (N : FiniteAdeleRing (𝓞 F) F) * (c * u) = u
        rw [← mul_assoc, hcN, one_mul]
      right_inv := fun u => by
        show c * ((N : FiniteAdeleRing (𝓞 F) F) * u) = u
        rw [← mul_assoc, hNc, one_mul]
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  have hint_c : IsCompact (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.Col.rlt_isCompact_intAd
  have hint_o : IsOpen (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.SG.Pf.top_isOpen_intAd F
  let D : κ → Set (FiniteAdeleRing (𝓞 F) F) := fun i =>
    (Homeomorph.subRight (w₀ i)) ⁻¹' (h ⁻¹' (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)))
  have hDc : ∀ i, IsCompact (D i) := fun i =>
    (Homeomorph.subRight (w₀ i)).isCompact_preimage.2 (h.isCompact_preimage.2 hint_c)
  have hDo : ∀ i, IsOpen (D i) := fun i =>
    (hint_o.preimage h.continuous).preimage (Homeomorph.subRight (w₀ i)).continuous
  have hint_l : IsClosed (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    (Formalism.UG.intAd F).toAddSubgroup.isClosed_of_isOpen hint_o
  have hDl : ∀ i, IsClosed (D i) := fun i =>
    (hint_l.preimage h.continuous).preimage (Homeomorph.subRight (w₀ i)).continuous
  refine ⟨Set.univ.pi D, isOpen_set_pi Set.finite_univ fun i _ => hDo i, isCompact_univ_pi hDc,
    isClosed_set_pi fun i _ => hDl i, fun i _ => ?_, fun u hu => hsub fun i _ => ?_⟩
  · show c * (w₀ i - w₀ i) ∈ (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F))
    rw [sub_self, mul_zero]
    exact zero_mem (Formalism.UG.intAd F)
  · have hi : c * (u i - w₀ i) ∈ Formalism.UG.intAd F := hu i (Set.mem_univ i)
    have h1 := Set.mem_iInter.mp (hNO _ hi) i
    rw [nsmul_eq_mul, ← mul_assoc, hcN, one_mul] at h1
    simpa using h1

theorem exists_bump : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : Set (κ → AF F)), IsOpen N → ∀ z₀ ∈ N, ∃ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N → Φ z = 0) ∧ 0 < (Φ z₀).re := by
  intro F _ _ κ _ N hN z₀ hz₀
  let P : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F) :=
    fun p i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  have hP : Continuous P := continuous_pi fun i =>
    Continuous.prodMk ((GlobalTheory.Core.Rk.RapidInt.continuous_ofMixed F).comp ((continuous_apply i).comp continuous_fst))
      ((continuous_apply i).comp continuous_snd)
  let y₀ : κ → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z₀ i).1
  let w₀ : κ → FiniteAdeleRing (𝓞 F) F := fun i => (z₀ i).2
  have hPz : ∀ z : κ → AdeleRing (𝓞 F) F,
      P (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1, fun i => (z i).2) = z := fun z =>
    funext fun i => Prod.ext (RingEquiv.symm_apply_apply _ _) rfl
  have hmem : P ⁻¹' N ∈ 𝓝 (y₀, w₀) :=
    (hN.preimage hP).mem_nhds (by show P (y₀, w₀) ∈ N; rw [hPz z₀]; exact hz₀)
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hmem
  obtain ⟨φ, hφs, hφc, hφd, hφr, hφ1⟩ := exists_contDiff_tsupport_subset (E := κ → mixedEmbedding.mixedSpace F) (n := ⊤) hA
  obtain ⟨C, hCo, hCc, hCcl, hwC, hCB⟩ := exists_compact_open_nhds F hB
  have hc : HasCompactSupport fun y => ((φ y : ℝ) : ℂ) :=
    hφc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  let f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφd)
  have hf : ∀ y, f y = ((φ y : ℝ) : ℂ) := fun y => rfl
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := Set.indicator C fun _ => 1
  have hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro hCc fun x hx => Set.indicator_of_notMem hx _⟩
    by_cases hx : x ∈ C
    · exact ⟨C, hCo, hx, fun x' hx' => by simp only [g, Set.indicator_of_mem hx, Set.indicator_of_mem hx']⟩
    · exact ⟨Cᶜ, hCcl.isOpen_compl, hx, fun x' hx' => by
        simp only [g, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']⟩
  have hval : ∀ z, GlobalTheory.WeilM.pureA F f g z = ((φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) : ℝ) : ℂ) *
      g (fun i => (z i).2) := fun z => rfl
  have hgval : ∀ w, g w = ((Set.indicator C (fun _ => (1 : ℝ)) w : ℝ) : ℂ) := fun w => by
    by_cases hw : w ∈ C <;> simp [g, hw]
  have hnn : ∀ y, 0 ≤ φ y := fun y => (hφr ⟨y, rfl⟩).1
  refine ⟨GlobalTheory.WeilM.pureA F f g, Submodule.subset_span ⟨f, g, hg, rfl⟩, fun z => ?_, fun z hz => ?_, ?_⟩
  · rw [hval, hgval, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨mul_nonneg (hnn _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _), rfl⟩
  · rw [hval]
    by_contra hne
    have h1 := left_ne_zero_of_mul hne
    have h2 := right_ne_zero_of_mul hne
    have h1' : φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) ≠ 0 := fun h => h1 (by rw [h]; simp)
    have h2' : (fun i => (z i).2) ∈ C := by
      by_contra h
      exact h2 (Set.indicator_of_notMem h _)
    have h3 := hAB (Set.mk_mem_prod (hφs (subset_tsupport _ h1')) (hCB h2'))
    apply hz
    have h4 : P (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1, fun i => (z i).2) ∈ N := h3
    rwa [hPz z] at h4
  · rw [hval]
    have e1 : g (fun i => (z₀ i).2) = 1 := Set.indicator_of_mem (show w₀ ∈ C from hwC) _
    have e2 : φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z₀ i).1) = 1 := hφ1
    rw [e1, e2]
    simp

end GlobalTheory.CompanionTheory.AdelicBump

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisActionStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformizer_galois_action : ∀ {l : ℕ} [Fact l.Prime] {K : FinExt l} {χ : ↥(GK K) →* (↥K.1)ˣ}, IsLTChar K χ →
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F (Om l)] [ValuativeExtension F (Om l)] [Algebra.IsAlgebraic F (Om l)],
    Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l)) →
    ∃ (π : 𝒪[F]) (hπ : Irreducible π), ∀ (g : Om l ≃ₐ[F] Om l) (g' : ↥(GK K)), (∀ y, g y = (g' : GQ l) y) →
      ∃ u : 𝒪[F]ˣ, algebraMap F (Om l) ((u : 𝒪[F]) : F) = (((χ g' : (↥K.1)ˣ) : ↥K.1) : Om l) ∧
        ∀ n, ∀ x ∈ lubinTateTorsion (Om l) (hπ := hπ) (isLubinTateSeries_ltPoly π) n,
          lubinTateGalPointMap (hπ := hπ) (isLubinTateSeries_ltPoly π) g x = (u : 𝒪[F]) • x := by
  first | exact @GlobalTheory.CompanionTheory.LTHodge.UnitAct.main | exact GlobalTheory.CompanionTheory.LTHodge.UnitAct.main | (intros; apply GlobalTheory.CompanionTheory.LTHodge.UnitAct.main <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueComplexPointUnder
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Under

open GlobalTheory.TuplePoint GlobalTheory.Points

theorem spZ_ext (f g : Sp ℂ ⟶ Sp ℤ) : f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  ext1
  exact Subsingleton.elim _ _

theorem top_ext {s s' : Γ(Sp ℂ, ⊤)} (h : valR (𝟙 (Sp ℂ)) ⊤ s = valR (𝟙 (Sp ℂ)) ⊤ s') : s = s' :=
  ext_of_dense (𝟙 (Sp ℂ)) fun _ => h

theorem hom_eq_of_val {N : ℕ} {φ ψ : Sp ℂ ⟶ PSpace ℤ N} (i : Fin (N + 1))
    (h₁ : ⊤ ≤ φ ⁻¹ᵁ chart ℤ N i) (h₂ : ⊤ ≤ ψ ⁻¹ᵁ chart ℤ N i)
    (h : ∀ j, valR φ (chart ℤ N i) (ratio ℤ N i j) = valR ψ (chart ℤ N i) (ratio ℤ N i j)) : φ = ψ := by
  refine GlobalTheory.ProjSpace.hom_ext (spZ_ext _ _) fun y => ⟨⊤, trivial, i, h₁, h₂, fun j => top_ext ?_⟩
  have e₁ := valR_appLE (𝟙 (Sp ℂ)) φ h₁ le_rfl (ratio ℤ N i j)
  have e₂ := valR_appLE (𝟙 (Sp ℂ)) ψ h₂ le_rfl (ratio ℤ N i j)
  rw [Category.id_comp] at e₁ e₂
  exact e₁.trans ((h j).trans e₂.symm)

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

abbrev blockVec (z : (Σ k, Bk n k) → ℂ) (k : Fin (m + 1)) : Fin (n k + 1) → ℂ := fun i => z ⟨k, i⟩

theorem blockVec_ne_zero {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : Fin (m + 1)) :
    blockVec z k ≠ 0 := fun h => by
  obtain ⟨i, hi⟩ := hz k
  exact hi (congrFun h i)

theorem isUnder_of_comp {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, blockVec z k ≠ 0) (y : CxPts (mpStr ℤ m n) σ₀)
    (h : ∀ k, y.1 ≫ prB n k = point ℤ (blockVec z k) (hz k)) : IsUnder y z := fun k i => by
  refine ⟨⟨fun hy => ne_zero_of_le (h k) hy le_rfl, fun hi => le_preimage_chart (h k) hi⟩, fun j hy => ?_⟩
  exact valR_pullRatio (h k) hy le_rfl j

theorem comp_of_isUnder {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, blockVec z k ≠ 0) (hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    {y : CxPts (mpStr ℤ m n) σ₀} (H : IsUnder y z) (k : Fin (m + 1)) :
    y.1 ≫ prB n k = point ℤ (blockVec z k) (hz k) := by
  obtain ⟨i, hi⟩ := hz' k
  have hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := ((H k i).1).2 hi
  refine hom_eq_of_val i (le_preimage_comp y.1 _ le_rfl hy)
    ((le_point_preimage_iff (o := ℤ) (ht := hz k) i).2 hi) fun j => ?_
  refine (valR_appLE y.1 (prB n k) le_rfl hy (ratio ℤ (n k) i j)).symm.trans ?_
  exact ((H k i).2 j hy).trans (valR_point_ratio (t := blockVec z k) (ht := hz k) hi j).symm

theorem existsUnique_isUnder (m : ℕ) (n : Fin (m + 1) → ℕ) (z : (Σ k, Bk n k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ∃! y : CxPts (mpStr ℤ m n) σ₀, IsUnder y z := by
  have ht := blockVec_ne_zero hz
  let a : ∀ k, Sp ℂ ⟶ PSpace ℤ (n k) := fun k => point ℤ (blockVec z k) (ht k)
  have ha : ∀ k, a k ≫ toSpecBase ℤ (n k) = spMap σ₀ := fun _ => spZ_ext _ _
  let y : CxPts (mpStr ℤ m n) σ₀ := ⟨lift m n (spMap σ₀) a ha, lift_mpStr m n _ a ha⟩
  have hy : ∀ k, y.1 ≫ prB n k = a k := lift_pr m n _ a ha
  refine ⟨y, isUnder_of_comp ht y hy, fun y' H => Subtype.ext ?_⟩
  exact GroundTheory.Arith.SchemeCoh.ProjSpace.hom_ext m n _ _ fun k =>
    (comp_of_isUnder ht hz H k).trans (hy k).symm

end GlobalTheory.CompanionTheory.MPDict.Under
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainSplitCentreProductStatement
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_split_centre_product : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure], IsFundamentalDomain (latticeGL E a) ((fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) '' (RightCosetSpace.fundamentalDomain (rationalGLOne (K := E) (n := a)) ×ˢ Set.Ico (0 : ℝ) 1)) μ := by
  first | exact @GlobalTheory.CompanionTheory.CuspTransfer.isFundamentalDomain_splitFd | exact GlobalTheory.CompanionTheory.CuspTransfer.isFundamentalDomain_splitFd | (intros; apply GlobalTheory.CompanionTheory.CuspTransfer.isFundamentalDomain_splitFd <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariantTotallyComplex
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.GAUnimod

theorem isMulRightInvariant_haar_GA : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure], μ.IsMulRightInvariant :=
  fun E _ _ _ N _ _ μ _ => GlobalTheory.CompanionTheory.PairDom.isMulRightInvariant_GA E N μ

end GlobalTheory.CompanionTheory.GAUnimod
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralSplitCentreInvariantStatement
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_split_centre_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL (K := E) (n := a))) [ν.IsHaarMeasure] (c : ENNReal), Measure.map (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ → ∀ φ : GA E a → ℂ, Continuous φ → (∀ t g, φ (splitCentre E a t * g) = φ g) → ∫⁻ g in ((fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) '' (RightCosetSpace.fundamentalDomain (rationalGLOne (K := E) (n := a)) ×ˢ Set.Ico (0 : ℝ) 1)), ‖φ g‖ₑ ^ 2 ∂(c • μ) = ∫⁻ x in RightCosetSpace.fundamentalDomain (rationalGLOne (K := E) (n := a)), ‖φ (x : GA E a)‖ₑ ^ 2 ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.CuspTransfer.lintegral_productDomain_norm_sq | exact GlobalTheory.CompanionTheory.CuspTransfer.lintegral_productDomain_norm_sq | (intros; apply GlobalTheory.CompanionTheory.CuspTransfer.lintegral_productDomain_norm_sq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankExtensionBoundStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_rank_extension_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V W₁ W₂ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂] (ρ : Representation ℂ (GL (Fin N) k) V) (π : Representation ℂ (GL (Fin N) k) W₁) (σ : Representation ℂ (GL (Fin N) k) W₂), IsSmooth ρ → Module.rank ℂ (TwJacquet ρ (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 → π.IsIrreducible → σ.IsIrreducible → IsSubquotient π ρ → IsSubquotient σ ρ → IsGenericFor ψ π → IsGenericFor ψ σ → Nonempty (π.Equiv σ) := by
  first | exact @GlobalTheory.CompanionTheory.GenUniq.nonempty_equiv_of_generic_subquotients | exact GlobalTheory.CompanionTheory.GenUniq.nonempty_equiv_of_generic_subquotients | (intros; apply GlobalTheory.CompanionTheory.GenUniq.nonempty_equiv_of_generic_subquotients <;> assumption)
end

