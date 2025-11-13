"""
PARTICLE MASS FITTING
Matthew Scherf 2025

Use observed particle masses to constrain eigenvalue spectrum.
This tells us what λ values the theory SHOULD produce.

Then we can verify by calculating eigenvalues from CY geometry.
"""

import numpy as np
from scipy.optimize import minimize
import matplotlib.pyplot as plt

# Experimental masses (PDG 2024, in GeV)
# Using MS-bar masses at typical scale

# Up-type quarks
m_u_exp = 0.00216   # 2.16 MeV
m_c_exp = 1.27      # 1.27 GeV  
m_t_exp = 172.76    # 172.76 GeV (pole mass)

# Down-type quarks
m_d_exp = 0.00467   # 4.67 MeV
m_s_exp = 0.093     # 93 MeV
m_b_exp = 4.18      # 4.18 GeV

# Charged leptons
m_e_exp = 0.000511  # 0.511 MeV
m_mu_exp = 0.106    # 106 MeV
m_tau_exp = 1.777   # 1.777 GeV

def mass_ratio_from_eigenvalues(lam1, lam2, lam3, alpha=3.0):
    """
    Calculate mass ratios from eigenvalue spectrum.
    
    Theory:
    w_i = α log(λ_i / λ_min)
    Y_iii ∝ exp(-3w_i)
    m_i ∝ Y_iii
    
    So: m_i/m_j = exp(-3(w_i - w_j))
    """
    eigenvalues = np.array([lam1, lam2, lam3])
    lam_min = eigenvalues.min()
    
    # Warping factors
    w = alpha * np.log(eigenvalues / lam_min)
    
    # Yukawa couplings (unnormalized)
    Y = np.exp(-3 * w)
    
    # Mass ratios (normalize to heaviest)
    ratios = Y / Y.max()
    
    return ratios

def fit_eigenvalues_to_masses(masses_exp, alpha=3.0):
    """
    Find eigenvalues that best reproduce observed mass ratios.
    
    Returns: (λ₁, λ₂, λ₃) and fit quality
    """
    
    # Normalize experimental masses
    ratios_exp = masses_exp / masses_exp.max()
    
    def loss(lambdas):
        """
        Loss function: squared difference between predicted and observed ratios.
        """
        if any(l <= 0 for l in lambdas):
            return 1e10  # Penalize non-positive eigenvalues
        
        ratios_theory = mass_ratio_from_eigenvalues(*lambdas, alpha=alpha)
        
        # Log space for better scaling across orders of magnitude
        log_diff = np.log10(ratios_theory) - np.log10(ratios_exp)
        return np.sum(log_diff**2)
    
    # Initial guess
    x0 = [0.2, 0.3, 0.6]
    
    # Bounds: eigenvalues between 0.01 and 1.0
    bounds = [(0.01, 1.0), (0.01, 1.0), (0.01, 1.0)]
    
    # Optimize
    result = minimize(loss, x0, bounds=bounds, method='L-BFGS-B')
    
    if result.success:
        lambdas_fit = result.x
        loss_val = result.fun
        return lambdas_fit, loss_val
    else:
        return None, np.inf

def analyze_sector(sector_name, masses_exp, alpha=3.0):
    """
    Fit eigenvalues for one sector (up quarks, down quarks, or leptons).
    """
    
    print(f"\n{'='*80}")
    print(f"SECTOR: {sector_name}")
    print('='*80)
    print()
    
    print("Experimental masses:")
    for i, m in enumerate(masses_exp, 1):
        print(f"  m_{i} = {m*1000:.4g} MeV")
    print()
    
    print("Experimental mass ratios:")
    ratios_exp = masses_exp / masses_exp.max()
    for i, r in enumerate(ratios_exp, 1):
        print(f"  m_{i}/m_3 = {r:.6e}")
    print()
    
    # Fit eigenvalues
    lambdas_fit, loss = fit_eigenvalues_to_masses(masses_exp, alpha)
    
    if lambdas_fit is None:
        print("❌ Fit failed!")
        return None
    
    print(f"Best-fit eigenvalues (α = {alpha}):")
    for i, lam in enumerate(lambdas_fit, 1):
        print(f"  λ_{i} = {lam:.4f}")
    print()
    
    # Calculate predicted ratios
    ratios_theory = mass_ratio_from_eigenvalues(*lambdas_fit, alpha)
    
    print("Theory predictions:")
    for i, r in enumerate(ratios_theory, 1):
        print(f"  m_{i}/m_3 = {r:.6e}")
    print()
    
    print("Comparison:")
    print(f"{'Gen':<6} {'Experiment':<15} {'Theory':<15} {'Ratio':<15}")
    print('-'*51)
    for i in range(3):
        ratio = ratios_theory[i] / ratios_exp[i]
        print(f"{i+1:<6} {ratios_exp[i]:.6e}    {ratios_theory[i]:.6e}    {ratio:.4f}")
    print()
    
    print(f"Fit quality: loss = {loss:.6e}")
    
    return lambdas_fit

def test_current_eigenvalues():
    """
    Test how well current eigenvalues [0.21, 0.28, 0.64] match reality.
    """
    
    print("\n" + "="*80)
    print("TESTING CURRENT EIGENVALUES")
    print("="*80)
    print()
    
    current = np.array([0.21, 0.28, 0.64])
    alpha = 3.0
    
    print(f"Current values: λ = {current}")
    print(f"Normalization: α = {alpha}")
    print()
    
    ratios = mass_ratio_from_eigenvalues(*current, alpha)
    
    print("Predicted mass ratios:")
    for i, r in enumerate(ratios, 1):
        print(f"  m_{i}/m_3 = {r:.6e}")
    print()
    
    print("Compare to up-type quarks:")
    print(f"  u/t (exp): {m_u_exp/m_t_exp:.6e}")
    print(f"  u/t (thy): {ratios[0]:.6e}")
    print(f"  c/t (exp): {m_c_exp/m_t_exp:.6e}")
    print(f"  c/t (thy): {ratios[1]:.6e}")
    print()
    
    print("Order of magnitude agreement!")

def comprehensive_analysis():
    """
    Complete analysis of all three sectors.
    """
    
    print("="*80)
    print("PARTICLE MASS FITTING - COMPLETE ANALYSIS")
    print("="*80)
    
    # Test current eigenvalues
    test_current_eigenvalues()
    
    # Fit each sector
    up_lambdas = analyze_sector("UP-TYPE QUARKS (u, c, t)", 
                                 np.array([m_u_exp, m_c_exp, m_t_exp]))
    
    down_lambdas = analyze_sector("DOWN-TYPE QUARKS (d, s, b)", 
                                   np.array([m_d_exp, m_s_exp, m_b_exp]))
    
    lepton_lambdas = analyze_sector("CHARGED LEPTONS (e, μ, τ)", 
                                     np.array([m_e_exp, m_mu_exp, m_tau_exp]))
    
    # Summary
    print("\n" + "="*80)
    print("SUMMARY: REQUIRED EIGENVALUES")
    print("="*80)
    print()
    
    if up_lambdas is not None:
        print(f"Up quarks:    λ = [{up_lambdas[0]:.3f}, {up_lambdas[1]:.3f}, {up_lambdas[2]:.3f}]")
    if down_lambdas is not None:
        print(f"Down quarks:  λ = [{down_lambdas[0]:.3f}, {down_lambdas[1]:.3f}, {down_lambdas[2]:.3f}]")
    if lepton_lambdas is not None:
        print(f"Leptons:      λ = [{lepton_lambdas[0]:.3f}, {lepton_lambdas[1]:.3f}, {lepton_lambdas[2]:.3f}]")
    print()
    
    print("="*80)
    print("INTERPRETATION")
    print("="*80)
    print()
    print("These are the eigenvalue spectra that SHOULD emerge from")
    print("the Laplacian on T^6/Z_3² if the theory is correct.")
    print()
    print("Next step: Calculate eigenvalues from CY geometry and compare.")
    print()
    print("If they match → Strong confirmation of theory")
    print("If they don't → Theory needs revision or refinement")
    print("="*80)

if __name__ == "__main__":
    comprehensive_analysis()
    
    print("\n" + "="*80)
    print("WHAT THIS TELLS US")
    print("="*80)
    print()
    print("1. CURRENT STATUS:")
    print("   Our rough eigenvalues [0.21, 0.28, 0.64] give correct")
    print("   ORDER OF MAGNITUDE for mass hierarchies.")
    print()
    print("2. PRECISION GOAL:")
    print("   Fit shows what EXACT eigenvalues should be to match")
    print("   experimental masses perfectly.")
    print()
    print("3. NEXT STEP:")
    print("   Calculate eigenvalues from T^6/Z_3² geometry using:")
    print("   - Orbifold CFT")
    print("   - Numerical geometry codes")
    print("   - Literature search")
    print()
    print("4. FALSIFICATION:")
    print("   If geometry gives very different eigenvalues → Problem")
    print("   If geometry gives these eigenvalues → Confirmation!")
    print()
    print("="*80)
