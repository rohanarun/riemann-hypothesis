module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1489
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsGermGIffExistsFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1482
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformArchimedeanCm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0871
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1418
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1475
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNonvanishingLineBundleInvMixOneZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

theorem isGen_oneGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen (Y := Y) L).IsGen := by
  intro i j
  have hg : (LB.LinComb L (Y := Y) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 :=
    by
    unfold LB.LinComb; simp
  simp only [LB.oneGen, hg, map_one, one_mul]

theorem exists_iso_mix_one_zero {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left)
    (hL : L.IsLB) : ∃ w : LB.Iso L (mix A L 1 0), w.IsGen := by
  have hs : LB.SameSum (K := PEmpty) PEmpty.elim PEmpty.elim
      (Sum.elim (fun _ : Fin 1 => 𝟙 A.left) ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left])
      (Sum.elim (fun _ => (1 : ℤ)) fun k => -(![1, 0] : Fin 2 → ℤ) k) := by
    intro ψ
    by_cases h : 𝟙 A.left = ψ <;> by_cases h' : (GrpObj.inv : A ⟶ A).left = ψ <;>
      simp [Fintype.sum_sum_type, Fin.sum_univ_two, h, h']
  obtain ⟨t, ht, -⟩ := ReciprocityTheory.ChartRestriction.G.DVR.gen_transport hL hs (LB.oneGen L) (isGen_oneGen L)
  have key := (GlobalTheory.GermSectionCompare.isGen_divEquiv ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![1, 0]
    ((GlobalTheory.GermSectionCompare.divEquiv ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![1, 0]).symm t)).1
    (by rw [Equiv.apply_symm_apply]; exact ht)
  exact ⟨_, key⟩

theorem nv_mix_one_zero : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (L : LB A.left), L.IsLB →
    ∀ j : ℕ, NV A L j → NV A (mix A L 1 0) j := by
  intro K _ A _ L hL j ⟨κ, lo, ft, W, hW, hcov, hne⟩
  obtain ⟨w, hw⟩ := exists_iso_mix_one_zero A L hL
  have hM : (mix A L 1 0).IsLB := LB.isLB_linComb hL _ _
  exact ⟨κ, lo, ft, W, hW, hcov, fun h => hne (h.of_iso (GlobalTheory.AbLaw.cechLBCongr A.hom W hL hM w hw).symm)⟩

end GlobalTheory.AmpleGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChooseMulComponentDegreeLeDimension
section
attribute [-instance] GlobalTheory.AdmLoc.modTens GlobalTheory.AdmLoc.modFun GlobalTheory.AdmLoc.modProd GlobalTheory.AdmLoc.modQuot GlobalTheory.AdmLoc.twistedModuleH1 GlobalTheory.AdmLoc.twistedSubmoduleH1 GlobalTheory.AdmLoc.moduleH1Alt
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

set_option autoImplicit false

namespace GlobalTheory.HSCore.CompShare

theorem share_of_data {F : Type} [Field F] [NumberField F] (X : Data F) {D δ T d : ℕ} (hD : X.D = D) (hT : X.T = T)
    (hd : X.d = d) (hδ : (δ : ℤ) = X.del) (h : (X.R : ℤ) * X.del ≤ X.d) : (T - 1).choose D * δ ≤ d := by
  subst hD hT hd
  rw [← hδ] at h
  exact_mod_cast h

theorem choose_mul_compDeg_le : Quoted → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : CompHS.WtPar Dw) (R : CompHS.Choice X Z U P) (ω : CompHS.CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : CompHS.Ready R ω x V dict) (f₁ : CompHS.CuspFrame Z U x V dict P.u₁) (f₂ : CompHS.CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : CompHS.Consts), IsNef c.F (h.data f₁ f₂ th k).LA → IsBig c.F (h.data f₁ f₂ th k).LA → (h.data f₁ f₂ th k).Birational → (P.T - 1).choose (CompHt.dimFlag Dw) * CompHt.compDeg U Z (AllWt.wtOf Dw P.u₁ 0) ≤ Module.finrank c.F (AllWt.cuspOn U Z (AllWt.wtOf Dw (P.wt P.T) 0)) := by
  intro hQ E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k hn hb hB
  have hp := GlobalTheory.CompHS.compPresents_data E H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k
  have hD : (h.data f₁ f₂ th k).D = CompHt.dimFlag Dw := hp.1
  have e := GlobalTheory.HSCore.ImageDegree.imageDeg_eq_del hQ c.F (h.data f₁ f₂ th k).toTuple _ _ _ _ _
    (h.data f₁ f₂ th k).geom hB hp.2
  refine share_of_data (h.data f₁ f₂ th k) hD rfl (h.d_eq f₁ f₂ th k) ?_ (_root_.GlobalTheory.HSCore.share_le hQ c.F _ hn hb)
  rw [← e, CompHt.compDeg, ← hD]

end GlobalTheory.HSCore.CompShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CondEIsCoprimeHalfDifferent
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.StdDatum.HalfDiff

theorem isCoprime_of_natCast_mem {D : D7} {I : Ideal (𝓞 D.host.E)} {N : ℕ} (hN : Nat.Coprime N (D.host.QS * D.host.q))
    (hI : (N : 𝓞 D.host.E) ∈ I) : IsCoprime I D.host.𝔟 := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
  have hb : D.host.𝔟 ≤ M := le_sup_right.trans hle
  have h0 : M ≠ ⊥ := fun e => ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D (eq_bot_iff.2 (e ▸ hb))
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨M, hM.isPrime, h0⟩
  exact GlobalTheory.HalfCompare.not_mem_of_coprime P hN (GlobalTheory.HalfCompare.two_q_mem (P := P) (Ideal.dvd_iff_le.2 hb))
    (hle (Ideal.mem_sup_left hI))

theorem coprime_of_mod {a b m : ℕ} (h : a % m = 1) (hb : b ∣ m) : Nat.Coprime a b := by
  have : Nat.Coprime a m := by rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h, Nat.gcd_one_left]
  exact this.coprime_dvd_right hb

theorem exists_nat_mem_place_coprime {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (h : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ P.S0) :
    ∃ p : ℕ, Nat.Coprime p (D.host.QS * D.host.q) ∧ ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  have hg : ∀ k, Nat.Coprime (D.host.g k) (D.host.QS * D.host.q) := fun k =>
    coprime_of_mod (D.ntypes.g_cond k) (dvd_mul_right _ _)
  rcases P.mem_S0_of_sum_eq.1 hv with rfl | h1
  · exact ⟨q0 D, coprime_of_mod (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
      (Dvd.dvd.mul_left ⟨D.host.d, rfl⟩ _), P.basePlace_over_qZero⟩
  · rcases (S1_mem_OmF D).1 h1 with h' | h' | h' | h'
    · exact ⟨_, hg 0, h'⟩
    · exact ⟨_, hg 1, h'⟩
    · exact ⟨_, h.1, h'⟩
    · exact ⟨_, h.2, h'⟩

theorem exists_nat_mem_condE {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (h : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) :
    ∃ N : ℕ, Nat.Coprime N (D.host.QS * D.host.q) ∧ (N : 𝓞 D.host.E) ∈ SqNum.condE P := by
  classical
  choose! p hp hm using fun v (hv : v ∈ P.S0) => exists_nat_mem_place_coprime P h hv
  refine ⟨∏ v ∈ P.S0, p v ^ condExp P v, Nat.Coprime.prod_left fun v hv => (hp v hv).pow_left _, ?_⟩
  unfold SqNum.condE
  push_cast
  refine Ideal.prod_mem_prod fun v hv => Ideal.pow_mem_pow ?_ _
  have h1 : ((p v : ℕ) : 𝓞 D.host.F) ∈ ((P.w v).under (𝓞 D.host.F)).asIdeal := by
    rw [P.under_w hv]; exact hm v hv
  simpa using Ideal.mem_comap.1 h1

theorem condE_isCoprime_halfDifferent {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (h : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) :
    IsCoprime (SqNum.condE P) D.host.𝔟 ∧ IsCoprime (D.host.conj • SqNum.condE P) D.host.𝔟 := by
  obtain ⟨N, hN, hm⟩ := exists_nat_mem_condE P h
  refine ⟨isCoprime_of_natCast_mem hN hm, isCoprime_of_natCast_mem hN ?_⟩
  have h1 := Ideal.smul_mem_pointwise_smul D.host.conj _ _ hm
  have h2 : D.host.conj • (N : 𝓞 D.host.E) = N := map_natCast (MulSemiringAction.toRingHom _ _ D.host.conj) N
  rwa [h2] at h1

end GlobalTheory.FunObj.StdDatum.HalfDiff

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformRealLinesCmExtension
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

namespace GlobalTheory.ThetaSmoothCM

theorem contDiff_thetaTr_real_CM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L →
            (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
            ∀ w, ContDiff ℝ ∞ fun t => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (w + L t) := by
  intro F E _ _ _ _ _ σ B hgood nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ hψ JA JB ξ hJA hJB κ _ co hrat φ hφ k L hLc hLf w
  exact _root_.GlobalTheory.ThetaSmoothF.contDiff_thetaTr_realF F E σ B hgood hψ nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ JA JB ξ hJA hJB κ co hrat φ hφ k L hLc hLf w

end GlobalTheory.ThetaSmoothCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformRationalDarbouxCm
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ThetaTrContCM

theorem continuous_thetaTr_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          Continuous (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hs hψ JA JB ξ hA hBm κ _ co hco φ hφ
  exact GlobalTheory.ThetaTrContF.continuous_thetaTrF F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hs JA JB ξ hA hBm κ co hco φ hφ

end GlobalTheory.ThetaTrContCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.StdDatum

variable (D : D7)

def cosetV (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) (o a d : ℕ) (e0 : VC D a d → ℂ) : VC D a d → ℂ :=
  ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
    Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o a d))
      (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0)

def congLev (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) : Subgroup (GA D N) :=
  Subgroup.closure {k | k ∈ intG D N ∧ CongOne D 𝔪 k}

def blockLev (𝔪 : Ideal (𝓞 D.host.E)) (d a : ℕ) : Subgroup (GA D d) :=
  Subgroup.closure {h | h ∈ intG D d ∧ ∀ i j : Fin d, j.1 < a → a ≤ i.1 →
    ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪}

variable {D}

def stdSum {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)) (o : ℕ)
    (R : Finset (GA D a)) : VC D a d → ℂ :=
  ∑ r ∈ R, W.Om r 1 (cosetV D δ 𝔪 o a d e0)

theorem congLev_le (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) : congLev D 𝔪 N ≤ intG D N :=
  (Subgroup.closure_le _).2 fun _ h => h.1

theorem blockLev_le (𝔪 : Ideal (𝓞 D.host.E)) (d a : ℕ) : blockLev D 𝔪 d a ≤ intG D d :=
  (Subgroup.closure_le _).2 fun _ h => h.1

end GlobalTheory.FunObj.StdDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspBlockConstantTermFormula
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open MeasureTheory

namespace GlobalTheory.BlockForms.CuspConst

theorem continuous_unip (E : Type) [Field E] [NumberField E] (d r' : ℕ) :
    Continuous fun x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E => GlobalTheory.CuspRep.unip x := by
  have hn : Continuous fun x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E => (GlobalTheory.CuspRep.nilM x : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Ad E)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [GlobalTheory.CuspRep.nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add hn
  · exact continuous_const.sub hn


end GlobalTheory.BlockForms.CuspConst

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRapidDecaySiegelConeRealPoints
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem cuspForm_rapidDecay_siegel : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∀ t : ℝ, 0 < t → ∀ lam : Fin a → ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∏ i, r i = 1 → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * ∏ i, r i ^ lam i := by
  intro hP E _ _ _ a ψ hψ Ω hΩ t ht lam
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.AutGrowth.uniform_growth_of_autForm hP E a ψ hψ.1
  obtain ⟨m, C1, hC1, hreal⟩ := _root_.GlobalTheory.rapidDecay_real a t ht lam N
  obtain ⟨B, hB1, hB⟩ := _root_.GlobalTheory.AutGrowth.height_mul_le_of_isCompact E a Ω hΩ
  obtain ⟨C0, hC0⟩ := hN []
  simp only [List.map_nil, List.prod_nil, Module.End.one_apply] at hC0
  have hC0' : ∀ y, ‖ψ.1 (infGL E a y)‖ ≤ max C0 0 * height y ^ N := fun y =>
    (hC0 y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (by linarith [one_le_height y]) _))
  have hex : ∀ i j : Fin a, ∃ C : ℝ, 0 ≤ C ∧ ((j : ℕ) = i + 1 → ∀ (r : Fin a → ℝ)
      (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
      d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) →
      ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) ^ m * height d ^ N) := by
    intro i j
    by_cases hij : (j : ℕ) = i + 1
    · obtain ⟨C, hC, h⟩ := _root_.GlobalTheory.CuspRapid.iterated_decay hP E a N t ht i j hij m ψ hψ hN Ω hΩ
      exact ⟨C, hC, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => absurd h hij⟩
  choose Cf hCf0 hCf using hex
  have hS0 : 0 ≤ ∑ p : Fin a × Fin a, Cf p.1 p.2 := Finset.sum_nonneg fun p _ => hCf0 p.1 p.2
  have hK0 : 0 ≤ max C0 0 * B ^ N := mul_nonneg (le_max_right _ _) (pow_nonneg (by linarith) _)
  refine ⟨(max C0 0 * B ^ N + ∑ p : Fin a × Fin a, Cf p.1 p.2) * C1,
    mul_nonneg (add_nonneg hK0 hS0) hC1, ?_⟩
  intro r d hr hrt hd hprod c hc
  have hhd : height d ^ N ≤ (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N :=
    pow_le_pow_left₀ (by linarith [one_le_height d]) (GlobalTheory.T.height_positiveDiagonal_le_sum_add_inv E a r d hr hd) N
  have hP0 : 0 ≤ ∏ i, r i ^ lam i := Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hr i).le _
  have hsplit : (max C0 0 * B ^ N + ∑ p : Fin a × Fin a, Cf p.1 p.2) * C1 * ∏ i, r i ^ lam i
      = max C0 0 * B ^ N * (C1 * ∏ i, r i ^ lam i)
        + (∑ p : Fin a × Fin a, Cf p.1 p.2) * (C1 * ∏ i, r i ^ lam i) := by ring
  have hA := mul_nonneg hK0 (mul_nonneg hC1 hP0)
  have hB' := mul_nonneg hS0 (mul_nonneg hC1 hP0)
  rcases hreal r hr hrt hprod with h1 | ⟨i, j, hij, h2⟩
  · have hdc : height (d * c) ^ N ≤ (B * height d) ^ N :=
      pow_le_pow_left₀ (by linarith [one_le_height (d * c)]) (hB c hc d) N
    calc ‖ψ.1 (infGL E a (d * c))‖ ≤ max C0 0 * height (d * c) ^ N := hC0' _
      _ ≤ max C0 0 * (B * height d) ^ N := mul_le_mul_of_nonneg_left hdc (le_max_right _ _)
      _ = max C0 0 * B ^ N * height d ^ N := by rw [mul_pow]; ring
      _ ≤ max C0 0 * B ^ N * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N := mul_le_mul_of_nonneg_left hhd hK0
      _ ≤ max C0 0 * B ^ N * (C1 * ∏ i, r i ^ lam i) := mul_le_mul_of_nonneg_left h1 hK0
      _ ≤ _ := by rw [hsplit]; linarith
  · have hq : 0 ≤ (r j / r i) ^ m := pow_nonneg (div_nonneg (hr j).le (hr i).le) _
    have hle : Cf i j ≤ ∑ p : Fin a × Fin a, Cf p.1 p.2 :=
      Finset.single_le_sum (f := fun p : Fin a × Fin a => Cf p.1 p.2) (fun p _ => hCf0 p.1 p.2)
        (Finset.mem_univ (i, j))
    calc ‖ψ.1 (infGL E a (d * c))‖ ≤ Cf i j * (r j / r i) ^ m * height d ^ N :=
          hCf i j hij r d hr hrt hd c hc
      _ ≤ Cf i j * ((r j / r i) ^ m * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhd hq) (hCf0 i j)
      _ ≤ Cf i j * (C1 * ∏ i, r i ^ lam i) := mul_le_mul_of_nonneg_left h2 (hCf0 i j)
      _ ≤ (∑ p : Fin a × Fin a, Cf p.1 p.2) * (C1 * ∏ i, r i ^ lam i) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg hC1 hP0)
      _ ≤ _ := by rw [hsplit]; linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFgSubringDescentGroupSectionsCurveStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fg_subring_descent_group_sections_curve : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, 1 ≤ m → (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u → ∃ (R : Subring k) (G₁ : Over (Sp R)) (_ : GrpObj G₁), Algebra.FiniteType ℤ R ∧ IsUnit (m : R) ∧ IsCommMonObj G₁ ∧ Smooth G₁.hom ∧ IsSeparated G₁.hom ∧ QuasiCompact G₁.hom ∧ GeometricallyConnected (pullback.snd G₁.hom (spMap R.subtype)) ∧ SmoothOfRelativeDimension g (pullback.snd G₁.hom (spMap R.subtype)) ∧ (∃ s₁ : Finset (𝟙_ (Over (Sp R)) ⟶ G₁), s₁.card = s.card ∧ (∀ x ∈ s₁, x ^ m = 1) ∧ ∀ x ∈ s₁, ∀ y ∈ s₁, x ≠ y → spMap R.subtype ≫ x.left ≠ spMap R.subtype ≫ y.left) ∧ ∃ (P₁ : Polynomial R) (_ : P₁ ≠ 0) (u₁ : Sp (Localization.Away P₁) ⟶ G₁.left) (α β : R) (hα : IsUnit (Polynomial.evalRingHom α P₁)) (hβ : IsUnit (Polynomial.evalRingHom β P₁)), u₁ ≫ G₁.hom = spMap (algebraMap R (Localization.Away P₁)) ∧ spMap R.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁ ≠ spMap R.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁ := by
  first | exact @GlobalTheory.SpreadCurve.group_sections_curve_descend | exact GlobalTheory.SpreadCurve.group_sections_curve_descend | (intros; apply GlobalTheory.SpreadCurve.group_sections_curve_descend <;> assumption)
end

