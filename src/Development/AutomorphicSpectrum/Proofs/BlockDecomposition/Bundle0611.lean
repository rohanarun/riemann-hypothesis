module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0424
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0504
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0553
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEqSmulOfInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrict
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntOffOfSmul
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0560
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0602
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapTop
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0419
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0443
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0045
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import GroundTheory.GlobalFields.TateThesis.HeckeTheorem
public import GroundTheory.GlobalFields.TateThesis.Nonvanishing
public import GroundTheory.GlobalFields.TateThesis.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0600
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulLeftFin
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology SchwartzMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.AlgRich

variable {D : D7}

variable {a r t n : ℕ} {S : Finset (Pl D)} {e : AE D}

theorem theta_idem {θ : InfFam D} (hθ : IsInfFam θ) (hid : IsIdem S e) (τ : D.what₂.Tau) : θ τ (infPart D e) = 1 := by
  have h := ((GlobalTheory.StdUnn.RealComp.real_components D θ hθ).1 (e - 1)).1 (fun w => by
    rw [RingHom.map_sub, hid.1 w, map_one, sub_self])
  have h' := h τ
  rw [RingHom.map_sub, RingHom.map_sub, map_one, map_one, sub_eq_zero] at h'
  exact h'

theorem clopen_sep (D : D7) {x y : Af D.host.F ⊗[D.host.F] D.host.E} (h : x ≠ y) :
    ∃ U : Set (Af D.host.F ⊗[D.host.F] D.host.E), IsClopen U ∧ x ∈ U ∧ y ∉ U := by
  have hne : GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E x ≠ GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E y :=
    fun h' => h ((GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E).injective h')
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
  haveI : T2Space (Af D.host.F) := GlobalTheory.IntegralFinAdele.t2Space_finiteAdeleRing' D.host.F
  have hd : GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E y k - GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E x k ≠ 0 :=
    sub_ne_zero.2 hk.symm
  obtain ⟨G, hGo, hGs⟩ := GlobalTheory.SmallLevel.exists_open_subgroup D.host.F
    {GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E y k - GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E x k}ᶜ
    (isOpen_compl_singleton.mem_nhds (by simpa using hd.symm))
  have hGc : IsClosed (G : Set (Af D.host.F)) := G.isClosed_of_isOpen hGo
  have hcont : Continuous fun w => GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E w k -
      GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E x k :=
    ((continuous_apply k).comp (GlobalTheory.AfTensNbhd.continuous_coordEquiv _ _)).sub continuous_const
  refine ⟨(fun w => GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E w k -
      GlobalTheory.AfTensNbhd.coordEquiv D.host.F D.host.E x k) ⁻¹' G, ⟨hGc.preimage hcont, hGo.preimage hcont⟩, ?_, ?_⟩
  · simp
  · intro hy
    exact hGs hy rfl

theorem continuous_mul_left_fin (D : D7) (c : Af D.host.F ⊗[D.host.F] D.host.E) :
    Continuous fun y : Af D.host.F ⊗[D.host.F] D.host.E => c * y := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  exact continuous_const.mul continuous_id

theorem sep_pts {θ : InfFam D} (hθ : IsInfFam θ) (hid : IsIdem S e) (he : e * e = e) {p q : Mx D a n}
    (hp : e • p = p) (hq : e • q = q) (hpq : p ≠ q) {B : Mx D a n → ℂ} (hB : B ∈ schwartzA θ a n) (hG : Good S e B)
    (hC : HasCompactSupport B) (Bp : B p = 1) (Bq : B q = 1) :
    ∃ Φ ∈ schwartzA θ a n, Good S e Φ ∧ HasCompactSupport Φ ∧ Φ p ≠ Φ q := by
  have hsm : ∀ (x : Mx D a n) i j, (e • x) i j = e * x i j := fun _ _ _ => rfl
  by_cases hf : p.map (finPart D) = q.map (finPart D)
  · have hi : ¬ ∀ τ, compAt θ τ p = compAt θ τ q := fun h => hpq (GlobalTheory.StabAtPlace.mx_ext hθ hf h)
    simp only [not_forall] at hi
    obtain ⟨τ, hτ⟩ := hi
    obtain ⟨i, j, hij⟩ : ∃ i j, compAt θ τ p i j ≠ compAt θ τ q i j := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hτ (Matrix.ext hc)
    let L : (D.what₂.Tau → Fin a → Fin n → ℂ) →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => Fin n → ℂ) i).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin a → Fin n → ℂ) τ))
    refine ⟨_, GlobalTheory.CompanionTheory.WSum.mul_mem_schwartzA D θ a n L L.hasTemperateGrowth _ hB, ?_, hC.mul_left, ?_⟩
    · refine good_factor (M := fun x => L fun τ i j => compAt θ τ x i j) (fun x => ?_) hG
      show θ τ (infPart D (e * x i j)) = θ τ (infPart D (x i j))
      rw [map_mul, map_mul, theta_idem hθ hid, one_mul]
    · show compAt θ τ p i j * B p ≠ compAt θ τ q i j * B q
      rw [Bp, Bq, mul_one, mul_one]
      exact hij
  · obtain ⟨i, j, hij⟩ : ∃ i j, finPart D (p i j) ≠ finPart D (q i j) := by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hf (Matrix.ext hc)
    obtain ⟨U, hU, hxU, hyU⟩ := clopen_sep D hij
    have hI : IsLocallyConstant (U.indicator fun _ => (1 : ℂ)) :=
      (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hU).isLocallyConstant
    let H : (Fin a → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ :=
      fun y => U.indicator (fun _ => (1 : ℂ)) (finPart D e * y i j)
    have hH : IsLocallyConstant H := hI.comp_continuous
      ((continuous_mul_left_fin D _).comp ((continuous_apply j).comp (continuous_apply i)))
    have hval : ∀ {x : Mx D a n}, e • x = x → H (fun i j => finPart D (x i j)) = U.indicator (fun _ => (1 : ℂ)) (finPart D (x i j)) := by
      intro x hx
      show U.indicator (fun _ => (1 : ℂ)) (finPart D e * finPart D (x i j)) = _
      rw [← map_mul, ← hsm, hx]
    refine ⟨_, fin_mul_mem θ hH hB, ?_, hC.mul_left, ?_⟩
    · refine good_factor (M := fun x => H fun i j => finPart D (x i j)) (fun x => ?_) hG
      show U.indicator (fun _ => (1 : ℂ)) (finPart D e * finPart D (e * x i j)) =
        U.indicator (fun _ => (1 : ℂ)) (finPart D e * finPart D (x i j))
      rw [← map_mul, ← map_mul, ← mul_assoc, he]
    · show (H fun i j => finPart D (p i j)) * B p ≠ (H fun i j => finPart D (q i j)) * B q
      rw [hval hp, hval hq, Bp, Bq, Set.indicator_of_mem hxU, Set.indicator_of_notMem hyU]
      simp

theorem bump_of (hBump : BumpEx) {θ : InfFam D} (hθ : IsInfFam θ) (hid : IsIdem S e) {C : Set (Mx D a n)}
    (hC : IsCompact C) (hCi : ∀ x ∈ C, e • x = x) :
    ∃ Φ ∈ schwartzA θ a n, Good S e Φ ∧ HasCompactSupport Φ ∧ (∀ x, 0 ≤ (Φ x).re ∧ (Φ x).im = 0) ∧ ∀ x ∈ C, Φ x = 1 := by
  obtain ⟨η, hη⟩ := hBump D θ hθ a n S e hid C hC (fun x hx => intOff_of_smul hid (hCi x hx))
  obtain ⟨m1, m2, m3⟩ := row_prod (S := S) (e := e) (θ := θ) a η (fun i => ⟨(hη i).1, (hη i).2.1, (hη i).2.2.1⟩)
  refine ⟨_, m1, m2, m3, fun x => ?_, fun x hx => Finset.prod_eq_one fun i _ => (hη i).2.2.2.2 x hx⟩
  have e1 : (∏ i, η i (x.submatrix (fun _ => i) id)) = ((∏ i, (η i (x.submatrix (fun _ => i) id)).re : ℝ) : ℂ) := by
    push_cast
    exact Finset.prod_congr rfl fun i _ => Complex.ext (by simp) (by simpa using (hη i).2.2.2.1 _ |>.2.2)
  show 0 ≤ (∏ i, η i (x.submatrix (fun _ => i) id)).re ∧ (∏ i, η i (x.submatrix (fun _ => i) id)).im = 0
  rw [e1, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨Finset.prod_nonneg fun i _ => ((hη i).2.2.2.1 _).1, rfl⟩

theorem smul_jn (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) : e • jn hn x v = jn hn (e • x) (e • v) := by
  ext i j
  simp only [jn, Matrix.smul_apply, Matrix.submatrix_apply, id]
  generalize (finSumFinEquiv.trans (finCongr hn)).symm j = k
  cases k <;> simp

theorem isClosedEmbedding_jn (hn : r + t = n) (e : AE D) :
    Topology.IsClosedEmbedding (fun z : XS D a r t e => jn hn z.1.1 z.1.2) := by
  subst hn
  obtain ⟨-, -, h2, -⟩ := GlobalTheory.CompanionTheory.OrbUniq.mx_facts D a (r + t)
  obtain ⟨-, -, h2r, -⟩ := GlobalTheory.CompanionTheory.OrbUniq.mx_facts D a r
  obtain ⟨-, -, h2t, -⟩ := GlobalTheory.CompanionTheory.OrbUniq.mx_facts D a t
  haveI : IsTopologicalRing (AE D) := GlobalTheory.Doubling.isTopologicalRing_tens
  have hcl : IsClosed {z : Mx D a r × Mx D a t | e • z.1 = z.1 ∧ e • z.2 = z.2} :=
    (isClosed_eq ((continuous_const_smul e).comp continuous_fst) continuous_fst).inter
      (isClosed_eq ((continuous_const_smul e).comp continuous_snd) continuous_snd)
  have hs : Topology.IsClosedEmbedding (Subtype.val : XS D a r t e → Mx D a r × Mx D a t) := hcl.isClosedEmbedding_subtypeVal
  have hj : Continuous fun z : Mx D a r × Mx D a t => jn (rfl : r + t = r + t) z.1 z.2 := by
    refine continuous_matrix fun i j => ?_
    simp only [jn, Matrix.submatrix_apply, id]
    generalize (finSumFinEquiv.trans (finCongr (rfl : r + t = r + t))).symm j = k
    cases k with
    | inl k =>
      simp only [Matrix.fromCols_apply_inl]
      exact continuous_fst.matrix_elem i k
    | inr k =>
      simp only [Matrix.fromCols_apply_inr]
      exact continuous_snd.matrix_elem i k
  have hu : Continuous fun x : Mx D a (r + t) =>
      ((x.submatrix id (Fin.castAdd t) : Mx D a r), (x.submatrix id (Fin.natAdd r) : Mx D a t)) :=
    (continuous_id.matrix_submatrix _ _).prodMk (continuous_id.matrix_submatrix _ _)
  have hl : Function.LeftInverse (fun x : Mx D a (r + t) =>
      ((x.submatrix id (Fin.castAdd t) : Mx D a r), (x.submatrix id (Fin.natAdd r) : Mx D a t)))
      (fun z : Mx D a r × Mx D a t => jn (rfl : r + t = r + t) z.1 z.2) := by
    intro z
    refine Prod.ext ?_ ?_
    · ext i j
      simp [jn]
    · ext i j
      simp [jn]
  exact (hl.isClosedEmbedding hu hj).comp hs

theorem exists_of_mem_algA {θ : InfFam D} (hn : r + t = n) {f : XS D a r t e → ℂ}
    (hf : f ∈ algA (a := a) θ hn S e) :
    ∃ Φ ∈ schwartzA θ a n, Good S e Φ ∧ HasCompactSupport Φ ∧ f = fun z => Φ (jn hn z.1.1 z.1.2) := by
  induction hf using Submodule.span_induction with
  | mem f h => exact h
  | zero => exact ⟨fun _ => 0, (schwartzA θ a n).zero_mem, good_zero, HasCompactSupport.zero, rfl⟩
  | add f g _ _ h₁ h₂ =>
    obtain ⟨Φ, m1, g1, c1, rfl⟩ := h₁
    obtain ⟨Ψ, m2, g2, c2, rfl⟩ := h₂
    exact ⟨fun x => Φ x + Ψ x, (schwartzA θ a n).add_mem m1 m2, good_add g1 g2, c1.add c2, rfl⟩
  | smul c f _ h₁ =>
    obtain ⟨Φ, m1, g1, c1, rfl⟩ := h₁
    exact ⟨fun x => c * Φ x, (schwartzA θ a n).smul_mem c m1, good_smul c g1, c1.mul_left, rfl⟩

theorem algRich : IdemEx → BumpEx → TopX → AlgRich := by
  intro hI hBump _ D θ hθ a r t n hn S e hid
  have he : e * e = e := ((hI D S).2 e hid).1
  have hι := isClosedEmbedding_jn (D := D) (a := a) hn e
  have gen : ∀ Φ ∈ schwartzA θ a n, Good S e Φ → HasCompactSupport Φ →
      (fun z : XS D a r t e => Φ (jn hn z.1.1 z.1.2)) ∈ algA (a := a) θ hn S e :=
    fun Φ h1 h2 h3 => Submodule.subset_span ⟨Φ, h1, h2, h3, rfl⟩
  have hfix : ∀ z : XS D a r t e, e • jn hn z.1.1 z.1.2 = jn hn z.1.1 z.1.2 := fun z => by
    rw [smul_jn, z.2.1, z.2.2]
  refine ⟨⟨fun f hf => ?_, fun f hf g hg => ?_, fun f hf => ?_, fun x y hxy => ?_, fun C hC => ?_⟩,
    fun f hf => exists_of_mem_algA hn hf⟩
  · obtain ⟨Φ, h1, -, h3, rfl⟩ := exists_of_mem_algA hn hf
    exact ⟨(GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ a n Φ h1).1.comp hι.continuous,
      h3.comp_isClosedEmbedding hι⟩
  · obtain ⟨Φ, h1, h2, h3, rfl⟩ := exists_of_mem_algA hn hf
    obtain ⟨Ψ, k1, k2, k3, rfl⟩ := exists_of_mem_algA hn hg
    exact gen (fun x => Φ x * Ψ x) (mul_mem θ h1 k1) (good_mul h2 k2) h3.mul_right
  · obtain ⟨Φ, h1, h2, h3, rfl⟩ := exists_of_mem_algA hn hf
    exact gen (fun x => conj (Φ x)) (conj_mem θ h1) (good_conj h2) (h3.comp_left (map_zero _))
  · have hne : jn hn x.1.1 x.1.2 ≠ jn hn y.1.1 y.1.2 := fun h => hxy (hι.injective h)
    have hfin : ({jn hn x.1.1 x.1.2, jn hn y.1.1 y.1.2} : Set (Mx D a n)).Finite := by simp
    obtain ⟨B, b1, b2, b3, -, b5⟩ := bump_of hBump hθ hid hfin.isCompact (by
      rintro w (rfl | rfl)
      · exact hfix x
      · exact hfix y)
    obtain ⟨Φ, h1, h2, h3, h4⟩ := sep_pts hθ hid he (hfix x) (hfix y) hne b1 b2 b3 (b5 _ (by simp)) (b5 _ (by simp))
    exact ⟨_, gen Φ h1 h2 h3, h4⟩
  · obtain ⟨B, b1, b2, b3, b4, b5⟩ := bump_of hBump hθ hid (hC.image hι.continuous) (by
      rintro _ ⟨z, -, rfl⟩
      exact hfix z)
    exact ⟨_, gen B b1 b2 b3, fun z => b4 _, fun z hz => b5 _ ⟨z, hz, rfl⟩⟩

end GlobalTheory.CompanionTheory.AlgRich

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinTestTw

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.FC GlobalTheory.CompanionTheory.FinLevelTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

theorem exists_lift (Y : ∀ w : Pl E, GLw n w) (hc : ∀ᶠ w : Pl E in cofinite, Y w ∈ GlobalTheory.LFun.KGL w (n := n)) :
    ∃ x : GL (Fin n) (Af E), ∀ w, GeneralLinearGroup.map (pLoc E w) x = Y w := by
  let M : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => (Y w).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => ((Y w)⁻¹).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).2 i j⟩
  have hloc : ∀ P Q : Matrix (Fin n) (Fin n) (Af E), (∀ w : Pl E, P.map (pLoc E w) = Q.map (pLoc E w)) → P = Q :=
    fun P Q h => Matrix.ext fun i j => Subtype.ext (funext fun w => congrFun (congrFun (h w) i) j)
  have hMM' : M * M' = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).mul_inv
  have hM'M : M' * M = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).inv_mul
  exact ⟨⟨M, M', hMM', hM'M⟩, fun w => Units.ext (Matrix.ext fun i j => rfl)⟩

theorem eventually_mem_KGL (g : GL (Fin n) (Af E)) :
    ∀ᶠ w : Pl E in cofinite, GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have h1 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w (g.1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => (g.1 i j).2
  have h2 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w ((g⁻¹).1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => ((g⁻¹).1 i j).2
  filter_upwards [h1, h2] with w h1 h2
  exact GlobalTheory.EulerTwRestr.mem_KGL_iff.2 ⟨fun i j => by rw [GlobalTheory.EulerTwRestr.loc_val]; exact h1 i j,
    fun i j => by rw [GlobalTheory.EulerTwRestr.loc_inv_val]; exact h2 i j⟩

theorem coe_pair_compact_subgroup (a b : ℕ) (w : Pl E) : (K2 a b w : Set (GLw a w × GLw b w)) =
    (GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)) ×ˢ (GlobalTheory.LFun.KGL w (n := b) : Set (GLw b w)) := Subgroup.coe_prod _ _

theorem mem_prod_Kf {x : Gf E a b} :
    x ∈ (Kf E a).prod (Kf E b) ↔ ∀ w : Pl E, atHom a b w x ∈ K2 a b w := by
  simp only [Subgroup.mem_prod, Kf, Subgroup.mem_iInf, Subgroup.mem_comap, forall_and]
  rfl

theorem isRestrW (a b : ℕ) :
    GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch (Gf E a b)) (atHom (E := E) a b) (K2 a b) := by
  have hset : {x : Gf E a b | ∀ w : Pl E, atHom a b w x ∈ K2 a b w} =
      (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) :=
    Set.ext fun x => (mem_prod_Kf (x := x)).symm.trans Subgroup.mem_prod
  refine ⟨fun w => w.elim, continuous_atHom, fun w => ?_, fun w => ?_, fun x y _ H => ?_, fun x => ?_, fun c y hy => ?_, ?_, fun C _ => ?_⟩
  · rw [coe_pair_compact_subgroup]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1
  · rw [coe_pair_compact_subgroup]
    exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
  · exact Prod.ext (GlobalTheory.EulerTwRestr.gl_ext fun w => congrArg Prod.fst (H w))
      (GlobalTheory.EulerTwRestr.gl_ext fun w => congrArg Prod.snd (H w))
  · filter_upwards [eventually_mem_KGL x.1, eventually_mem_KGL x.2] with w h1 h2
    exact ⟨h1, h2⟩
  · obtain ⟨x₁, h₁⟩ := exists_lift (fun w => (y w).1) (hy.mono fun w h => h.1)
    obtain ⟨x₂, h₂⟩ := exists_lift (fun w => (y w).2) (hy.mono fun w h => h.2)
    exact ⟨(x₁, x₂), fun w => w.elim, fun w => Prod.ext (h₁ w) (h₂ w)⟩
  · rw [hset]
    exact GlobalTheory.CompanionTheory.EulerV.isOpen_Kf.prod GlobalTheory.CompanionTheory.EulerV.isOpen_Kf
  · have e : {x : Gf E a b | (∀ w, GlobalTheory.RestrMeas.noArch (Gf E a b) w x ∈ C w) ∧ ∀ w : Pl E, atHom a b w x ∈ K2 a b w} =
        (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) := by
      rw [← hset]
      exact Set.ext fun x => ⟨fun h => h.2, fun h => ⟨fun w => w.elim, h⟩⟩
    rw [e]
    exact GlobalTheory.CompanionTheory.EulerV.isCompact_Kf.prod GlobalTheory.CompanionTheory.EulerV.isCompact_Kf

theorem eventually_eq_indicator {φ : Fam E a b} (h : IsTestP φ) :
    ∀ᶠ w : Pl E in cofinite, φ w = (K2 a b w : Set (GLw a w × GLw b w)).indicator 1 := by
  obtain ⟨K₁, K₂, -, -, h⟩ := h
  exact h.2

theorem hasCompactSupport_loc {φ : Fam E a b} (h : IsTestP φ) (w : Pl E) : HasCompactSupport (φ w) := by
  obtain ⟨K₁, K₂, -, -, h⟩ := h
  exact (h.1 w).1

theorem factors_ne_zero {S : Set (Pl E)} {φ₁ φ₂ : Fam E a b} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) {y : Gf E a b}
    (hy : finFn S φ₁ φ₂ y ≠ 0) (w : Pl E) (hw : w ∈ S) :
    φ₁ w (atW w y) ≠ 0 ∧ (IsSplitAt w → φ₂ w (atW w (thP E a b y)) ≠ 0) := by
  set g : Pl E → ℂ := fun w => φ₁ w (atW w y) * if IsSplitAt w then φ₂ w (atW w (thP E a b y)) else 1 with hg
  have hone : ∀ᶠ w in cofinite, g w = 1 := by
    filter_upwards [eventually_eq_indicator h₁, eventually_eq_indicator h₂, (isRestrW a b).eventually_mem y,
      (isRestrW a b).eventually_mem (thP E a b y)] with w e₁ e₂ m₁ m₂
    have m₁' : atW w y ∈ (K2 a b w : Set (GLw a w × GLw b w)) := m₁
    have m₂' : atW w (thP E a b y) ∈ (K2 a b w : Set (GLw a w × GLw b w)) := m₂
    simp only [hg]
    rw [e₁, e₂, Set.indicator_of_mem m₁', Set.indicator_of_mem m₂']
    simp
  have hfin : (S ∩ Function.mulSupport g).Finite :=
    (eventually_cofinite.1 hone).subset fun w hw => hw.2
  have hz : g w ≠ 0 := by
    intro h0
    apply hy
    change ∏ᶠ w ∈ S, g w = 0
    rw [finprod_mem_eq_prod g hfin]
    exact Finset.prod_eq_zero (hfin.mem_toFinset.2 ⟨hw, by simp [Function.mem_mulSupport, h0]⟩) h0
  refine ⟨left_ne_zero_of_mul hz, fun hs => ?_⟩
  have hz' := right_ne_zero_of_mul hz
  rwa [if_pos hs] at hz'

end GlobalTheory.CompanionTheory.FinTestTw

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityOfColouring
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProdCell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_class_of_degree (n : ℕ) (t : IrrGL (k := k)) (h : t.1 = n) :
    ∃ u : IrrCl (GL (Fin n) k), (⟨n, u⟩ : IrrGL (k := k)) = t := by
  subst h
  exact ⟨t.2, rfl⟩

theorem subsingleton_irrCl_of_eq_zero (n : ℕ) (h : n = 0) : Subsingleton (IrrCl (GL (Fin n) k)) := by
  subst h
  exact GlobalTheory.SmGL.SegModel.subsingleton_irrCl_zero

theorem class_eq_of_sigma_eq (t : IrrGL (k := k)) (z : IrrCl (GL (Fin t.1) k))
    (h : (⟨t.1, z⟩ : IrrGL (k := k)) = t) : z = t.2 :=
  eq_of_heq (Sigma.ext_iff.1 h).2


set_option maxHeartbeats 1600000 in
theorem jhMult_cell_colour : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (x : Fin h → IrrGL (k := k)) (W : List (IrrGL (k := k))) (b : Fin h → Fin W.length → ℕ) (hrow : ∀ i, ∑ j, b i j = (x i).1) (hcol : ∀ j, ∑ i, b i j = (W.get j).1) (c : Fin W.length → Fin h), (∀ i j, b i j = if c j = i then (W.get j).1 else 0) → jhMult (piTensor fun j => (W.get j).rep) (cellFunctor (c := fun i j => Fin (b i j)) (fun i => stdBlocks (b i) (hrow i)) (fun j => stdBlocks (fun i => b i j) (hcol j)) (piTensor fun i => (x i).rep)) = ∏ i, jmL (sub W c i) (x i).rep := by
  intro k _ _ _ _ h x W b hrow hcol c hb
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hC : CellSemisimplification k := (GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).2
  obtain ⟨T, hT0, hT⟩ := hC (Fin h) (Fin W.length) (fun i => Fin (x i).1) (fun j => Fin (W.get j).1)
    (fun i j => Fin (b i j)) (fun i => stdBlocks (b i) (hrow i))
    (fun j => stdBlocks (fun i => b i j) (hcol j)) (fun i => (x i).2.rep.V) (fun i => (x i).rep)
    (fun i => (x i).2.rep.smooth) (fun i => (x i).2.rep.hasFiniteLength)
  have hirr : (piTensor fun j => (W.get j).rep).IsIrreducible :=
    _root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k _ _ fun j => (W.get j).2.rep
  let τ : IrrRep (Levi k fun j => Fin (W.get j).1) :=
    ⟨_, piTensor fun j => (W.get j).rep, isSmooth_piTensor fun j => (W.get j).2.rep.smooth, hirr⟩
  refine (hT τ).trans ?_
  have hzero : ∀ i j, c j ≠ i → b i j = 0 := fun i j hij => by rw [hb, if_neg hij]

  have hcolumn : ∀ (s : ∀ i j, IrrCl (GL (Fin (b i j)) k)) (j : Fin W.length),
      ∃ z : IrrCl (GL (Fin (W.get j).1) k), (⟨_, z⟩ : IrrGL (k := k)) = ⟨b (c j) j, s (c j) j⟩ ∧
        Nonempty ((multiProd (stdBlocks (fun i => b i j) (hcol j))
          fun i => (s i j).rep.ρ).Equiv z.rep.ρ) := fun s j =>
    GlobalTheory.T.product_single_nonzero_factor_equiv (fun i => (⟨b i j, s i j⟩ : IrrGL (k := k))) (hcol j) (c j)
      fun i hi => hzero i j (Ne.symm hi)

  have hex : ∀ i j, ∃ u : IrrCl (GL (Fin (b i j)) k),
      c j = i → (⟨b i j, u⟩ : IrrGL (k := k)) = W.get j := by
    intro i j
    by_cases hij : c j = i
    · obtain ⟨u, hu⟩ := exists_class_of_degree (b i j) (W.get j) (by rw [hb, if_pos hij])
      exact ⟨u, fun _ => hu⟩
    · exact ⟨(IrrRep.det (Fin (b i j)) 1 isSmoothChar_one).cl, fun h' => absurd h' hij⟩
  choose s₀ hs₀ using hex
  have hfirst : ∀ i, jhMult (piTensor fun j => (s₀ i j).rep.ρ)
      (GlobalTheory.SmGL.jac (stdBlocks (b i) (hrow i)) (x i).rep) = jmL (sub W c i) (x i).rep := fun i =>
    GlobalTheory.T.jacquet_multiplicity_sublist_padding W c i (fun j => (⟨b i j, s₀ i j⟩ : IrrGL (k := k))) (fun j hj => hs₀ i j hj)
      (fun j hj => hzero i j hj) (hrow i) (x i).rep
  rw [Finset.sum_eq_single s₀]
  · choose z hz e using hcolumn s₀
    have hzW : ∀ j, z j = (W.get j).2 := fun j =>
      class_eq_of_sigma_eq _ _ ((hz j).trans (hs₀ (c j) j rfl))
    have hsecond : jhMult τ.ρ (piTensor fun j =>
        multiProd (stdBlocks (fun i => b i j) (hcol j)) fun i => (s₀ i j).rep.ρ) = 1 := by
      have a : (piTensor fun j => multiProd (stdBlocks (fun i => b i j) (hcol j))
          fun i => (s₀ i j).rep.ρ).Equiv (piTensor fun j => (W.get j).rep) :=
        LocGL.piTensorEquiv fun j => (e j).some.trans (by rw [hzW j]; exact .refl _)
      exact (jhMult_congr_right _ a).trans (jhMult_self hirr)
    rw [hsecond, mul_one]
    exact Finset.prod_congr rfl fun i _ => hfirst i
  · intro s _ hs
    refine mul_eq_zero_of_right _ ?_
    choose z hz e using hcolumn s
    have a : (piTensor fun j => multiProd (stdBlocks (fun i => b i j) (hcol j))
        fun i => (s i j).rep.ρ).Equiv (piTensor fun j => (z j).rep.ρ) :=
      LocGL.piTensorEquiv fun j => (e j).some
    refine (jhMult_congr_right _ a).trans ?_
    by_contra hne
    obtain ⟨φ⟩ := (jhMult_ne_zero_iff.1 hne).nonempty_equiv hirr
      (_root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k _ _ fun j => (z j).rep)
    have hcl : ∀ j, (W.get j).2 = z j := fun j => by
      have := _root_.GlobalTheory.TensorFactorUnique.cl_eq_of_piTensor_equiv _ (fun j => GL (Fin (W.get j).1) k) (fun j => (W.get j).2.rep)
        (fun j => (z j).rep) ⟨φ.symm⟩ j
      rwa [IrrCl.cl_rep, IrrCl.cl_rep] at this
    refine hs (funext fun i => funext fun j => ?_)
    by_cases hij : c j = i
    · subst hij
      have h1 : (⟨b (c j) j, s (c j) j⟩ : IrrGL (k := k)) = ⟨b (c j) j, s₀ (c j) j⟩ := by
        rw [hs₀ (c j) j rfl, ← hz j, ← hcl j]
      exact eq_of_heq (Sigma.mk.inj_iff.1 h1).2
    · haveI := subsingleton_irrCl_of_eq_zero (k := k) (b i j) (hzero i j hij)
      exact Subsingleton.elim _ _
  · intro hs
    obtain ⟨i, hi⟩ := hT0 s₀ hs
    exact mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ i) hi) _

end GlobalTheory.CompanionTheory.FineProdCell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalFunctionalEquationH1
section
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar partialLFunction coe_localChar continuous_localChar)
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.HeckePartial

end GlobalTheory.CompanionTheory.HeckePartial

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSpectralOfStrictExponentStatement
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_spectral_of_strict_exponent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.StandardFunctorsFiniteLength → Zls.MaxExpStrict π → Zls.HeckeSpectral π := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBound.heckeSpectral_of_maxExpStrict | exact GlobalTheory.CompanionTheory.HeckeBound.heckeSpectral_of_maxExpStrict | (intros; apply GlobalTheory.CompanionTheory.HeckeBound.heckeSpectral_of_maxExpStrict <;> assumption)
end

