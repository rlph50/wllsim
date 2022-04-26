#include <cstdlib>
#include <iostream>
#include <fstream>
#include <cstdio>
#include <complex.h>
#include <ctime>
#include <ratio>
#include <chrono>
#include <random>
#include <cmath>
#include <string.h>

#include <nlopt.h>
#include <fftw3.h>

using namespace std;

// SER_LEN is the max length of a series - used for initializing array sizes ec
#define SER_LEN 8190
// When we generate a new realisation, we generate then throw away the first GEN_SIZE points. This forms a run-in period for the process.
#define GEN_SIZE 1024
// used for setting array sizes etc
#define MAX_TRIALS 1000

// Next we use these as upper limits on the effort taken by the optimisation routines.
#define MAXTIME 15
#define MAXEVAL 5000
#define TOL 1.0e-12

// Variance Gamma Distribution parameters
#define VG_THETA (-0.5)
#define VG_NU 1.5
#define VG_SIGMA2 1


unsigned int ser_len=SER_LEN; // actual length of series.

unsigned int which_min(double *x, unsigned int n) {
    double minVal=*x;
    int minIndex=0;
    for (unsigned int j=1;j<n;j++)
        if (x[j]<minVal) {
            minVal=x[j];
            minIndex=j;
            }
    return(minIndex);
    };
unsigned int which_max(double *x, unsigned int n) {
    double maxVal=*x;
    int maxIndex=0;
    for (unsigned int j=1;j<n;j++)
        if (x[j]>maxVal) {
            maxVal=x[j];
            maxIndex=j;
            }
    return(maxIndex);
    };

double digamma ( double x, int *ifault )

/******************************************************************************/
/*
  Purpose:

    DIGAMMA calculates DIGAMMA ( X ) = d ( LOG ( GAMMA ( X ) ) ) / dX

  Licensing:

    This code is distributed under the GNU LGPL license.

  Modified:

    20 March 2016

  Author:

    Original FORTRAN77 version by Jose Bernardo.
    C version by John Burkardt.

  Reference:

    Jose Bernardo,
    Algorithm AS 103:
    Psi ( Digamma ) Function,
    Applied Statistics,
    Volume 25, Number 3, 1976, pages 315-317.

  Parameters:

    Input, double X, the argument of the digamma function.
    0 < X.

    Output, int *IFAULT, error flag.
    0, no error.
    1, X <= 0.

    Output, double DIGAMMA, the value of the digamma function at X.
*/
{
  static double c = 8.5;
  static double euler_mascheroni = 0.57721566490153286060;
  double r;
  double value;
  double x2;
/*
  Check the input.
*/
  if ( x <= 0.0 )
  {
    value = 0.0;
    *ifault = 1;
    return value;
  }
/*
  Initialize.
*/
  *ifault = 0;
/*
  Use approximation for small argument.
*/
  if ( x <= 0.000001 )
  {
    value = - euler_mascheroni - 1.0 / x + 1.6449340668482264365 * x;
    return value;
  }
/*
  Reduce to DIGAMA(X + N).
*/
  value = 0.0;
  x2 = x;
  while ( x2 < c )
  {
    value = value - 1.0 / x2;
    x2 = x2 + 1.0;
  }
/*
  Use Stirling's (actually de Moivre's) expansion.
*/
  r = 1.0 / x2;
  value = value + log ( x2 ) - 0.5 * r;

  r = r * r;

  value = value
    - r * ( 1.0 / 12.0
    - r * ( 1.0 / 120.0
    - r * ( 1.0 / 252.0
    - r * ( 1.0 / 240.0
    - r * ( 1.0 / 132.0 ) ) ) ) );

  return value;
}

void ggbr_coef(unsigned int n, double d, double u, double *res) {
    // Populate "res" with n gegenbauer coefficients for d, u
    // implemented using the recursion formula for the coefficients.
    double ld, lu;

    ld=d;
    lu=u;
    res[0]=1.0l;
    res[1]=2.0l*ld*lu;
    res[2]=2.0l*ld*(1.0l+ld)*lu*lu-ld;
    for (unsigned int i=3;i<n;i++) {
        double temp=(ld-1.0l)/((double) i);
        res[i]=2.0l*lu*(temp+1.0l)*res[i-1]-(2.0l*temp+1.0l)*res[i-2];
        };
};


class cSimulate {
// This class generates a new realisation of a Gegenbauer k=2 white noise proces.
public:
    // variance-gamma distribution parameters
    // These are set to the estimated ones for the S&P data from Senata (2004)
    double vg_theta = VG_THETA, vg_nu = VG_NU, vg_sigma2 = VG_SIGMA2;

private:
    double d1,u1,d2,u2,sigma2, series_var, true_phi;
    unsigned int n, gen_size;
    double *phi;
    double *p;
    unsigned int distribution=0; // Gaussian by default
    double sum_sq_ggbr_coef(unsigned int n, double d, double u) {
        double *c=(double *)malloc(sizeof(double)*n);
        double sum=0.0;

        ggbr_coef(n,d,u, c);
        for (unsigned int i=0;i<n;i++) sum+=c[i]*c[i];
        free(c);
        return (sum);
    };
    void calc_acf(unsigned int n) {
        // calc Eqn 3.5 of Woodward, Cheng and Gray, 1998. Also Ford 1991.
        // reverses Spectrum p to the underlying ACF via simple numerical integration- trapezoidal rule.
        unsigned int m=10000;

        for (unsigned int k=0; k<n; k++) {
            double y=0.0l, lastOmega=0.0l;
            double lastPf=pow( 4.0l*(1.0l-u1)*(1.0l-u1), -d1)*pow( 4.0l*(1.0l-u2)*(1.0l-u2), -d2);
            for (unsigned int f=1; f<=m; f++) {
                long double f_n=((long double) f)/((long double) (2*m));
                long double omega=2.0l*M_PI*f_n;
                long double temp1=cos(omega)-u1, temp2=cos(omega)-u2;
                if (fabs(temp1)>1.0e-200&&fabs(temp2)>1.0e-200) {
                    long double Pf=pow(4.0l*temp1*temp1,-d1)*pow(4.0l*temp2*temp2,-d2)*cos(omega*((long double) k));
                    y+= (lastPf+Pf)/2.0l*(omega-lastOmega);
                    lastPf = Pf;
                    lastOmega = omega;
                    }
                };
            g[k]=y/M_PI;
            };
    };
    void acf_normalise() {
        // scale ACF so that first element is 1.0
        double g_max;
        g_max=fabs(*g);
        // Now scale everything down by g_max
        for (unsigned int i=0;i<2*gen_size;i++) g[i]=g[i]/g_max;
    };
    void DurbinLevinson() {
        // As documented by Hosking 1984 section 3.
        // Given an ACF, generate a process with that ACF.
        // We allow for a number of distributions.
        double Nt, Dt, m=0.0,v=1.0,sd=1.0;
        double *oldphi=(double *)malloc(gen_size*sizeof(double));
        unsigned seed1 = std::chrono::system_clock::now().time_since_epoch().count();
        std::mt19937_64 mersene_generator (seed1);  // mt19937 is a standard mersenne_twister_engine
        std::normal_distribution<double> xform_gaussian(0.0,1.0);
        std::student_t_distribution<double> xform_student(5.0);
        std::student_t_distribution<double> xform_student2(2.0);
        std::student_t_distribution<double> xform_student3(6.0);
        std::chi_squared_distribution<double> xform_chi_sq(1.0);
        std::chi_squared_distribution<double> xform_chi_sq3(3.0);
        std::uniform_real_distribution<double> uniform(-0.5,0.5);
        double gamma_alpha=0.25, gamma_beta=2.0;
        std::gamma_distribution<double> xform_gamma(gamma_alpha,gamma_beta);
        std::gamma_distribution<double> xform_gamma_changed(gamma_alpha/2.0,gamma_beta);
        double gamma_alpha_3=3.0, gamma_beta_3=2.0;
        std::gamma_distribution<double> xform_gamma3(gamma_alpha_3,gamma_beta_3);

        // Variance Gamma RVs
        // Using the algorithm documented by Madden Carr & Chung (1998)
        double vg_factor = 0.5*sqrt(vg_theta*vg_theta+2.0*vg_sigma2/vg_nu);
        double vg_mu_p = vg_factor+vg_theta/2.0;
        double vg_mu_n = vg_factor-vg_theta/2.0;
        double vg_nu_p = 1.0/(vg_mu_p*vg_mu_p*vg_nu);
        double vg_nu_n = 1.0/(vg_mu_n*vg_mu_n*vg_nu);
        double vg_sd   = sqrt(vg_theta*vg_theta*vg_nu+vg_sigma2);
        std::gamma_distribution<double> gamma_p(vg_mu_p,vg_nu_p);
        std::gamma_distribution<double> gamma_n(vg_mu_n,vg_nu_n);

        Nt=0.0; Dt=1.0;
#ifdef NO_SIGMA
        v=1.0;
#else
        v=sigma2*series_var;
#endif
        if (distribution==0) {
            xform_gaussian.reset();
            y[0]=xform_gaussian(mersene_generator)*sqrt(v);
            }
        if (distribution==1)
            y[0]=xform_student(mersene_generator)*sqrt(v);
        if (distribution==2)
            y[0]=xform_chi_sq(mersene_generator)/sqrt(2.0)*sqrt(v);
        if (distribution==3)
            y[0]=xform_student2(mersene_generator)*sqrt(v);
        if (distribution==4) {
            xform_gaussian.reset();
            double temp=xform_gaussian(mersene_generator);
            y[0]=temp*temp*sqrt(v);
            }
        if (distribution==5)
            y[0]=xform_chi_sq3(mersene_generator)/sqrt(6.0)*sqrt(v);
        if (distribution==6)
            y[0]=(gamma_p(mersene_generator)-gamma_n(mersene_generator))/vg_sd*sqrt(v);
        if (distribution==7)
            y[0]= (xform_gamma(mersene_generator)-gamma_alpha/gamma_beta)/(sqrt(gamma_alpha)*gamma_beta)*sqrt(v);
        if (distribution==8) {
            // Laplace distribution. We generate this directly from the Uniform Distribution.
            double u = uniform(mersene_generator);
            double sign_u = 1.0;
            if (u<0.0) sign_u = (-1);
            double laplace_rv = -sign_u/sqrt(2.0l)*log(1.0-2.0*fabs(u));
            y[0]= laplace_rv*sqrt(v);
            }
        if (distribution==9)
            y[0]=xform_student2(mersene_generator)*sqrt(v)/sqrt(1.5);
        if (distribution==10)
            y[0]= (xform_gamma(mersene_generator)-gamma_alpha/gamma_beta)/(sqrt(gamma_alpha)*gamma_beta)*sqrt(v);
        if (distribution==11)
            y[0]= (xform_gamma3(mersene_generator)-gamma_alpha_3/gamma_beta_3)/(sqrt(gamma_alpha_3)*gamma_beta_3)*sqrt(v);

        for (unsigned int t=1;t<gen_size;t++) {
            double sum=0.0;
            for (unsigned int j=0;j<t;j++) oldphi[j]=phi[j];
            for (unsigned int j=1;j<t;j++) sum+=(oldphi[j]*g[t-j]);
            Dt-=Nt*Nt/Dt;
            Nt=g[t]-sum;
            phi[t]=Nt/Dt;
            for (unsigned int j=1;j<t;j++)
                phi[j]=oldphi[j] - (phi[t]*oldphi[t-j]);
            m=0.0;
            for (unsigned int j=1;j<=t;j++) m+=(phi[j]*y[t-j]);
            v*=(1-phi[t]*phi[t]);
            sd=sqrt(v);
            if (distribution==0)
                y[t]=(xform_gaussian(mersene_generator)*sd)+m;
            if (distribution==1)
                y[t]=(xform_student(mersene_generator)*sd)+m;
            if (distribution==2)
                y[t]=(xform_chi_sq(mersene_generator)/sqrt(2.0)*sd)+m;
            if (distribution==3)
                y[t]=(xform_student2(mersene_generator)*sd)+m;
            if (distribution==4) {
                double temp=xform_gaussian(mersene_generator);
                y[t]=temp*temp*sd+m;
                }
            if (distribution==5)
                y[t]=(xform_chi_sq3(mersene_generator)/sqrt(6.0)*sd)+m;
            if (distribution==6)
                y[t]=(gamma_p(mersene_generator)-gamma_n(mersene_generator))/vg_sd*sd+m;
            if (distribution==7)
                y[t]= ((xform_gamma(mersene_generator)-gamma_alpha/gamma_beta)/(sqrt(gamma_alpha)*gamma_beta))*sd+m;
            if (distribution==8) {
                // Laplace distribution. We generate this directly from the Uniform Distribution.
                double u = uniform(mersene_generator);
                double sign_u = 1.0;
                if (u<0.0) sign_u = (-1);
                double laplace_rv = -sign_u/sqrt(2.0l)*log(1.0-2.0*fabs(u));
                y[t] = laplace_rv*sd + m;
                }
            if (distribution==9)
                y[t]=xform_student3(mersene_generator)*sd/sqrt(1.5)+m;
            if (distribution==10) {
                if (t<=(n/2)+(GEN_SIZE/4))
                    y[t]= ((xform_gamma(mersene_generator)-gamma_alpha/gamma_beta)/(sqrt(gamma_alpha)*gamma_beta))*sd+m;
                else
                    y[t]= ((xform_gamma_changed(mersene_generator)-0.5*gamma_alpha/gamma_beta)/(sqrt(gamma_alpha/2.0)*gamma_beta))*sd+m;
                }
            if (distribution==11)
                y[t]= ((xform_gamma3(mersene_generator)-gamma_alpha_3/gamma_beta_3)/(sqrt(gamma_alpha_3)*gamma_beta_3))*sd+m;
            };
        //for (unsigned int i=0;i<n;i++) if (isnan(y[i])) cout << "Nan y[" << i <<"] v=" << v << endl;
        free(oldphi);
    };


public:
    double *y, *z, g[2*SER_LEN+2];
    cSimulate(int init_n, double init_d1, double init_u1, double init_d2, double init_u2, double init_phi, double init_sigma2, unsigned int init_dist) {
        // Algorithm here is that we generate GEN_SIZE+SER_LEN obs but for half the power function.
        // otherwise power function repeats itself.
        n=init_n;
        gen_size=n+GEN_SIZE;
        d1=init_d1;
        u1=init_u1;
        d2=init_d2;
        u2=init_u2;
        true_phi = init_phi;
        sigma2=init_sigma2;
        distribution=init_dist;
        y=(double *)malloc(gen_size*sizeof(double));
        z=(double *)malloc(gen_size*sizeof(double));
        phi=(double *)malloc(gen_size*sizeof(double));
        for (unsigned int i=0;i<gen_size;i++) y[i]=phi[i]=0.0;
        for (unsigned int i=0;i<2*ser_len+2;i++) g[i]=0.0;
        calc_acf(2*gen_size);
        series_var=g[0];    // save for later
        acf_normalise();
        };
    ~cSimulate() {
        free(y);
        free(z);
        free(phi);
        };
    void GenerateProcess() {
        DurbinLevinson();
        if (GEN_SIZE>0) {
            for (unsigned int i=0;i<n;i++) y[i]=y[i+(GEN_SIZE/4)];
            for (unsigned int i=n;i<n+(GEN_SIZE/2);i++) y[i]=0.0;
            }
        // Now we implement the AR(1) component
        z[0]=y[0];
        for (unsigned int i=1; i<n; i++) z[i]=y[i] + true_phi*z[i-1];
        for (unsigned int i=0; i<n; i++) y[i]=z[i];
        }
};

typedef struct {
    unsigned int n, m, n_calls;
    double *spec, *y, *cos_2_pi_f, *logSpec, u, d, sigma2;
    } seriesParams;

class cSeriesStats {
// part of estimation process - find series stats - acf periodogram etc.
// we use a standard object in part to ensure all the estimation methods have exactly the same stats to work with,
// and they have exactly the same overhead in terms of producing those stats.
public:
    int n, m, nm, kn;
    bool est_u, est_d, est_sigma2, est_with_delta;
    double *freq, *cos_2_pi_f, *spec, *logSpec, *aggSpec, *logAggSpec, *cos_2_pi_fk, *y, *g;

    cSeriesStats(unsigned int init_n, double *init_y, int smoothing) {
        y=init_y;
        n=init_n;
        m=smoothing;
        if (m>0) {
            kn=n/(2*m);
            nm=2*m*kn;
            }
        else {
            kn=n/2;
            nm=2*kn;
            };

        freq=(double *)malloc((n+1)*sizeof(double));
        spec=(double *)malloc((n+1)*sizeof(double));
        cos_2_pi_f=(double *)malloc((n+1)*sizeof(double));
        logSpec=(double *)malloc((n+1)*sizeof(double));
        aggSpec=(double *)malloc((n+1)*sizeof(double));
        logAggSpec=(double *)malloc((n+1)*sizeof(double));
        cos_2_pi_fk=(double *)malloc((n+1)*sizeof(double));
        g=(double *)malloc((n+1)*sizeof(double));
        calcACF();
        calcSpectrum();
        if (m>0)
            calcAggSpec();
       };
    ~cSeriesStats() {
        free(freq);
        free(spec);
        free(cos_2_pi_f);
        free(logSpec);
        free(aggSpec);
	free(logAggSpec);
        free(cos_2_pi_fk);
        free(g);
        };
    void calcSpectrum() {
        fftw_complex *in, *out;
        fftw_plan plan;
        in = (fftw_complex*) fftw_malloc(sizeof(fftw_complex) * SER_LEN);
        for (int i=n-1;i>=0;i--) {in[i][0]=y[i]; in[i][1]=0.0;};
        out = (fftw_complex*) fftw_malloc(sizeof(fftw_complex) * SER_LEN);
        plan = fftw_plan_dft_1d(n, in, out, FFTW_FORWARD, FFTW_ESTIMATE);
        fftw_execute(plan);
        for (int i=0;i<n;i++) {
            freq[i]=((double) i)/((double) n);
            cos_2_pi_f[i]=cos(2.0*M_PI*freq[i]);
            spec[i]=(out[i][0]*out[i][0]+out[i][1]*out[i][1])/(2.0*M_PI*((double) n));
            logSpec[i]=log(spec[i]);
            };
        fftw_destroy_plan(plan);
        fftw_free(in); fftw_free(out);
    };
    void calcAggSpec(){
        // as per paper. We aggregate together periodogram ordinates
        for (int k=1;k<=kn;k++) {
            double sum=0.0;
            int mk=m*k;
            for (int j=m*(k-1)+1; j<=mk; j++)
                sum+=spec[j];
            aggSpec[k-1]=sum; ///dm;
            logAggSpec[k-1]=log(aggSpec[k-1]);
            cos_2_pi_fk[k-1]= cos(M_PI*((double) (2*k-1))/((double) (2*kn)));
        }
    };
    double mean() {
        double sum=y[0];
        for (int i=1;i<n;i++) sum+=y[i];
        return(sum/((double) n));
        };
    double processVar() {
        double m=mean();
        double sum=0.0l;
        for (int i=0;i<n;i++) {
            double temp=y[i]-m;
            sum+= temp*temp;
            }
        sum/=((double) n);
        return(sum);
    };
    void calcACF() {
        double m=mean();
        for (int k=0;k<n;k++) g[k]=0.0;
        for (int k=0;k<n/2;k++) {
            double sum=0.0l;
            unsigned int nk= n;
            for (unsigned int i=0;i<nk;i++) sum+= (y[i]-m)*(y[(i+k)%n]-m);
            g[k]=sum/((double) nk);
            }
    };
};


class cCSSEst {
// Estimate parameters of a realisation using methof of Chung (1996)
private:
    double *y;  // pointer to array of realisations.
    double calc_d1, calc_u1, calc_d2, calc_u2, calc_phi, calc_sigma2, calc_min_lse;
    unsigned int n;
    cSeriesStats *ss;

    static void calc_ma_errors(unsigned int n, double d, double u, double phi, double *y, double *eps) {
        // This routine reverses the "y" realisations to find the errors
        // under the assumption that the process is ggbr k=2 white noise.
        double *c=(double *)malloc(sizeof(double)*n);
        //double sum;
        //double *eps=(double *)malloc(sizeof(double)*(n)); // this will be the wn process errors
        (*eps) = (*y);                  // eps[0]=y[0]
        //double res= 0.0l;               // y[0]^2

        ggbr_coef(n,d,u, c);
        for (unsigned int t=1;t<n;t++) {
            double sum=0.0l;
            for (unsigned int j=1;j<=t;j++)
                sum+=c[j]*eps[t-j];
            eps[t]=(y[t]-phi*y[t-1]-sum);
            //res+=eps_ar1*eps_ar1;
            };
        //free(eps);
        free(c);
    };
    static double css_lse(unsigned dimSize, const double* x, double* grad, void* f_data){
        // Calculate the lse - "S" function in Chungs notation.
        // This is the function to be minimised.
        double d1=x[0];
        double u1=x[1];
        double d2=x[2];
        double u2=x[3];
        double phi=x[4];
        //double sigma2=x[5];

        // Check parameters are within range; if not then move them so they are. any nan values mean we return an nan.
        if (isnan(d1)) return(d1);
        if (isnan(u1)) return(u1);
        if (isnan(d2)) return(d2);
        if (isnan(u2)) return(u2);
        if (isnan(phi)) return(phi);
        //if (isnan(sigma2)) return(sigma2);

        if (u1>1.0) u1=1.0-1.0e-20;
        if (u1<0.0) u1=0.0;
        if (d1<0.0) d1=1.0e-20;
        if (d1>0.5) d1=0.5-1.0e-20;
        if (u2>1.0) u2=1.0-1.0e-20;
        if (u2<0.0) u2=0.0;
        if (d2<0.0) d2=1.0e-20;
        if (d2>0.5) d2=0.5-1.0e-20;
        if (phi>1.0) phi=1.0-1.0e-20;
        if (phi< -1.0) phi= -1.0+1.0e-20;
        //if (sigma2<1.0e-20)  sigma2=1.0e-20;

        double res;
        seriesParams *sp1 = (seriesParams *) f_data;
        unsigned int n=sp1->n;
        //double dn2=((double) n)/2.0;
        double *y=sp1->y;

        res=0.0l;
        double *eps1=(double *)malloc(sizeof(double)*n);
        double *eps2=(double *)malloc(sizeof(double)*n);
        calc_ma_errors(n,d1,u1,phi,y, eps1);
        calc_ma_errors(n,d2,u2,0.0l,eps1, eps2);
        for (unsigned int i=1;i<n-1;i++) {
            double temp=eps2[i];
            res+=temp*temp;
            }
        free(eps1);
        free(eps2);
        //cout << "CSS res=" << res << " d1=" << d1 << " u1=" << u1 << " d2=" << d2 << " u2=" << u2 << " sigma2=" << sigma2 << endl;
        if (isnan(res)||!isfinite(res)||fabs(res)>1.0e100)
            cerr << "CSS LSE NAN\n";
        return (res);
    };
    // Since we have 2 spikes, we insist the algorithm gives them to us in a particular order, and min separation
    static double css_u_seq_constraint(unsigned n, const double *x, double *grad, void *data)
        {
            return(x[1]-x[3]+0.05);     // Ensure a minimum separation
         }
public:
    seriesParams sp;
    nlopt_result optResult;
    double timeTaken=0.0;

    cCSSEst(unsigned int init_n, double *init_y) {
        y=init_y;
        n=init_n;
        ss = new cSeriesStats(init_n, init_y, 0);
        sp.y=init_y;
        sp.n=init_n;
        findMinLSE();
       };
    ~cCSSEst() {
        ss->~cSeriesStats();
    };
    void findMinLSE() {
        using namespace std::chrono;
        // Start Timer...
        steady_clock::time_point startTime = steady_clock::now();

        double x[]={0.25,0.5,0.25,0.5,0.0};  // we initialise x to give us standard initial values.
        double lse_val=0.0;
        double lse_val_c=0.0;
        double lb[]={1.0e-20,0.05,1.0e-20,0.05,-1.0};
        double ub[]={0.5-1.0e-20,0.95,0.5-1.0e-20,0.95,1.0};

        // Now minimise lse() function
        // First step is to identify the region of the parameter space with the global min.

        nlopt_opt directOpt=nlopt_create(NLOPT_GN_DIRECT_NOSCAL,5);
        nlopt_set_min_objective(directOpt, css_lse, (void *) &sp);
        nlopt_set_lower_bounds(directOpt, lb);
        // DIRECT algorithm requires a bounded parameter space
        nlopt_set_upper_bounds(directOpt, ub);

        // DIRECT algorithm does not handle general inequality constraints.
        //nlopt_add_inequality_constraint(directOpt, whittle_u_seq_constraint, NULL, TOL);

        // Standard termination criteria
        nlopt_set_ftol_abs(directOpt, TOL);
        nlopt_set_maxtime(directOpt, MAXTIME);
        nlopt_set_maxeval(directOpt, MAXEVAL);
        // Now we optimise to get initial values
        optResult=nlopt_optimize(directOpt, x, &lse_val);
        nlopt_destroy(directOpt);

        // Now we see if we need to swap the params around if they are in the wrong order
        if (x[3]<x[1]) {// yes we need to swap them
            double temp0=x[0], temp1=x[1];
            x[0]=x[2]; x[1]=x[3];
            x[2]=temp0; x[3]=temp1;
        };

        // Now we get better accuracy by using a local optimisation method.
        nlopt_opt cobyLAOpt=nlopt_create(NLOPT_LN_COBYLA,5);
        nlopt_set_min_objective(cobyLAOpt, css_lse, (void *) &sp);
        nlopt_set_lower_bounds(cobyLAOpt, lb);
        nlopt_set_upper_bounds(cobyLAOpt, ub);
        nlopt_add_inequality_constraint(cobyLAOpt, css_u_seq_constraint, NULL, TOL);
        // Standard termination criteria
        nlopt_set_ftol_abs(cobyLAOpt, TOL);
        nlopt_set_maxtime(cobyLAOpt, MAXTIME);
        nlopt_set_maxeval(cobyLAOpt, MAXEVAL);

        optResult=nlopt_optimize(cobyLAOpt, x, &lse_val_c);
        nlopt_destroy(cobyLAOpt);

        calc_d1=x[0];
        calc_u1=x[1];
        calc_d2=x[2];
        calc_u2=x[3];
        calc_phi=x[4];
        calc_sigma2 = lse_val_c / ((double) n);
        calc_min_lse=lse_val_c;

        steady_clock::time_point endTime = steady_clock::now();
        duration<double> time_span = duration_cast<duration<double>>(endTime - startTime);
        timeTaken=(double)time_span.count();
    };
    double Optimal_d1() {return(calc_d1);};
    double Optimal_u1() {return(calc_u1);};
    double Optimal_d2() {return(calc_d2);};
    double Optimal_u2() {return(calc_u2);};
    double Optimal_phi() {return(calc_phi);};
    double Optimal_sigma2() {return(calc_sigma2);};
};

class cWHTLEst {
// Estimate parameters of a realisation using methof of Whittle as documented by Giraitis and Leipus (1995)
// and Ford (1991).
private:
    double *y;  // pointer to array of realisations.
    double calc_d1, calc_u1, calc_d2, calc_u2, calc_phi, calc_sigma2, calc_min_lse;
    unsigned int n, m;
    cSeriesStats *ss;

    static double spectral_density(double cos_omega, double d1, double u1, double d2, double u2, double phi) {
        // returns the value of the spectral density of a ggbr k=2 white noise process at a given frequency (cos_omega).
        // used by the "whittle_log_liklihood" function
        double temp1=cos_omega-u1;
        double temp2=cos_omega-u2;
        double ggbr_factor;
        if (fabs(temp1)<1.0e-20||fabs(temp2)<1.0e-20)
            ggbr_factor=1.0e200;
        else
            ggbr_factor=pow(4.0*temp1*temp1,-d1) * pow(4.0*temp2*temp2,-d2);
        return(ggbr_factor/(1.0-2.0*phi*cos_omega+phi*phi));
        }
    static double whittle_log_likelihood(unsigned dimSize, const double* x, double* grad, void* f_data){
        // This calculates the Whittle Log Liklihood, to be minimised to produce the parameter estimates.
        double d1=x[0];
        double u1=x[1];
        double d2=x[2];
        double u2=x[3];
        double phi=x[4];
        if (u1>1.0) u1=1.0-1.0e-20;
        if (u1<0.0) u1=0.0;
        if (d1<0.0) d1=1.0e-20;
        if (d1>0.5) d1=0.5-1.0e-20;
        if (u2>1.0) u2=1.0-1.0e-20;
        if (u2<0.0) u2=0.0;
        if (d2<0.0) d2=1.0e-20;
        if (d2>0.5) d2=0.5-1.0e-20;
        if (phi>1.0-1.0e-5) phi=1.0-1.0e-5;
        if (phi< -1.0+1.0e-5) phi= -1.0+1.0e-5;
        double res;
        seriesParams *sp1 = (seriesParams *) f_data;
        unsigned int n=sp1->n;

        res=0.0;
        for (unsigned int i=0;i<n;i++) {
            double f=spectral_density(sp1->cos_2_pi_f[i], d1, u1, d2, u2, phi);
            if ((f>1.0e-100)&&(!isnan(f))&&(!isinf(f)))
                res+= (log(f)+(sp1->spec[i])/f);
            }
        if (isnan(res)||isinf(res))
            cerr << "Whittle NAN\n";
        if (fabs(res)>1.0e200)
            cerr << "Whittle 1e200\n";
        return (-res/((double) n));
        };

    // Since we have 2 spikes, we insist the algorithm gives them to us in a particular order,
    static double whittle_u_seq_constraint(unsigned n, const double *x, double *grad, void *data)
        {
            return(x[1]-x[3]+0.05);     // Ensure a minimum separation
         }

public:
    seriesParams sp;
    nlopt_result optResult;
    double timeTaken=0.0;

    cWHTLEst(unsigned int init_n, double *init_y, int smoothing) {
        y=init_y;
        n=init_n;
        m=smoothing;
        if ((m<=0)|(m>(init_n/2))) m=1;
        ss = new cSeriesStats(init_n, init_y, m);
        sp.n=(m>1 ? (ss->kn):init_n);
        sp.m=smoothing;
        sp.y=init_y;
        sp.cos_2_pi_f=(m>1 ? (ss->cos_2_pi_fk):(ss->cos_2_pi_f));
        sp.spec=(m>1 ? ss->aggSpec:ss->spec);
        sp.logSpec=(m>1 ? ss->logAggSpec:ss->logSpec);
        findMaxLL();
       };
    ~cWHTLEst() {
        ss->~cSeriesStats();
    };
    void findMaxLL() {
        using namespace std::chrono;
        // Start Timer...
        steady_clock::time_point startTime = steady_clock::now();

        double x[]={0.25,0.5,0.25,0.5,0.0};  // we initialise x to give us standard initial values.
        double lse_val=0.0;
        double lse_val_c=0.0;
        double lb[]={1.0e-20,0.05,1.0e-20,0.05,-1.0};
        double ub[]={0.5-1.0e-20,0.95,0.5-1.0e-20,0.95,1.0};

        // Now minimise lse() function
        // First step is to identify the region of the parameter space with the global min.

        nlopt_opt directOpt=nlopt_create(NLOPT_GN_DIRECT_NOSCAL,5);
        nlopt_set_max_objective(directOpt, whittle_log_likelihood, (void *) &sp);
        // DIRECT algorithm requires a bounded parameter space
        nlopt_set_lower_bounds(directOpt, lb);
        nlopt_set_upper_bounds(directOpt, ub);

        // DIRECT algorithm does not handle general inequality constraints.
        //nlopt_add_inequality_constraint(directOpt, whittle_u_seq_constraint, NULL, TOL);

        // Standard termination criteria
        nlopt_set_ftol_abs(directOpt, TOL);
        nlopt_set_maxtime(directOpt, MAXTIME);
        nlopt_set_maxeval(directOpt, MAXEVAL);
        // Now we optimise to get initial values
        optResult=nlopt_optimize(directOpt, x, &lse_val);
        nlopt_destroy(directOpt);

        // Now we see if we need to swap the params around if they are in the "wrong" order
        if (x[3]<x[1]) {// yes we need to swap them
            double temp0=x[0], temp1=x[1];
            x[0]=x[2]; x[1]=x[3];
            x[2]=temp0; x[3]=temp1;
        };

        // Now we get better accuracy by using a local optimisation method.
        nlopt_opt cobyLAOpt=nlopt_create(NLOPT_LN_COBYLA,5);
        nlopt_set_max_objective(cobyLAOpt, whittle_log_likelihood, (void *) &sp);
        nlopt_set_lower_bounds(cobyLAOpt, lb);
        nlopt_set_upper_bounds(cobyLAOpt, ub);
        nlopt_add_inequality_constraint(cobyLAOpt, whittle_u_seq_constraint, NULL, TOL);
        // Standard termination criteria
        nlopt_set_ftol_abs(cobyLAOpt, TOL);
        nlopt_set_maxtime(cobyLAOpt, MAXTIME);
        nlopt_set_maxeval(cobyLAOpt, MAXEVAL);

        optResult=nlopt_optimize(cobyLAOpt, x, &lse_val_c);
        nlopt_destroy(cobyLAOpt);

        calc_d1=x[0];
        calc_u1=x[1];
        calc_d2=x[2];
        calc_u2=x[3];
        calc_phi=x[4];
        calc_sigma2 = 2.0*M_PI*(-lse_val_c);
        calc_min_lse=lse_val_c;

        steady_clock::time_point endTime = steady_clock::now();
        duration<double> time_span = duration_cast<duration<double>>(endTime - startTime);
        timeTaken=(double)time_span.count();
    };
    double Optimal_d1() {return(calc_d1);};
    double Optimal_u1() {return(calc_u1);};
    double Optimal_d2() {return(calc_d2);};
    double Optimal_u2() {return(calc_u2);};
    double Optimal_phi() {return(calc_phi);};
    double Optimal_sigma2() {return(calc_sigma2);};
};

class cBNPEst {
// This implements the new estimator for the parameters.
public:
    seriesParams sp;
    cSeriesStats *ss;

    unsigned int n;
    double opt_lse;
    double timeTaken=0.0;

    static double lse(unsigned dimSize, const double* x, double* grad, void* f_data){
        // This is the L" function of the paper - the sum of squares between the periodogram and the spectral density
        // assuming a ggbr white noise spectral density.
        double d1, u1, d2, u2, phi, sigma2;
        double res=0.0;
        seriesParams *sp1 = (seriesParams *) f_data;
        (sp1->n_calls)++;
        unsigned int n=(sp1->n), n2= ( (sp1->m)>1 ? n:(n/(sp1->m)));

        d1=x[0]; u1=x[1]; d2=x[2]; u2=x[3]; phi=x[4]; sigma2=x[5];
        if (isnan(d1)) return(d1);
        if (isnan(u1)) return(u1);
        if (isnan(d2)) return(d2);
        if (isnan(u2)) return(u2);
        if (isnan(phi)) return(phi);
        if (isnan(sigma2)) return(sigma2);

        if (u1>1.0) u1=1.0;
        if (u1<0.0) u1=0.0;
        if (d1<0.0) d1=1.0e-20;
        if (d1>0.5) d1=0.5-1.0e-20;
        if (u2>1.0) u2=1.0;
        if (u2<0.0) u2=0.0;
        if (d2<0.0) d2=1.0e-20;
        if (d2>0.5) d2=0.5-1.0e-20;
        if (phi> 1.0-1.0e-5) phi=1.0-1.0e-5;
        if (phi< -1.0+1.0e-5) phi= -1.0+1.0e-5;
        if (sigma2<1.0e-20) sigma2=1.0e-20;

        double logSigma2=log(sigma2/(2.0*M_PI));
        double *cos_2_pi_f=sp1->cos_2_pi_f;
        double *logSpec=sp1->logSpec;

        for (unsigned int i=1;i<n2;i++) {
            double temp1=cos_2_pi_f[i]-u1;
            double temp2=cos_2_pi_f[i]-u2;
            if (fabs(temp1)>=1.0e-200&&fabs(temp2)>=1.0e-200) {
                double log_temp1=log(4.0*temp1*temp1);
                double log_temp2=log(4.0*temp2*temp2);
                double temp3=logSpec[i] - (logSigma2-log(1.0-2.0*phi*cos_2_pi_f[i]+phi*phi)-d1*log_temp1-d2*log_temp2);
                res+= temp3*temp3;
                }
            };
        if (res<0.0)
            cerr << "BNP res<0\n";
        res=sqrt(fabs(res));
        if (isnan(res))
            cerr << "BNP LSE NAN\n";
        if (fabs(res)>1.0e100)
            cerr << "BNP LSE " << res << endl;
        return (res);
    };

    // Since we have 2 spikes, we insist the algorithm gives them to us in a particular order,
    static double bnp_u_seq_constraint(unsigned n, const double *x, double *grad, void *data)
        {
            return(x[1]-x[3]+0.05);
         }

private:
    double calc_u1=0.0, calc_d1=0.0, calc_u2=0.0, calc_d2=0.0, calc_sigma2=1.0, calc_phi=0.0, calc_min_lse=0.0;
    int m, kn, nm;

nlopt_result findMinLSE() {
        using namespace std::chrono;
        // Start Timer...
        steady_clock::time_point startTime = steady_clock::now();

        double x[]={0.25,0.5,0.25,0.5,0.0,0.5};  // we initialise x to give us standard initial values.
        double lse_val=0.0;
        double lse_val_c=0.0;
        double lb[]={1.0e-20,0.05,1.0e-20,0.05,-1.0,1.0e-20};
        double ub[]={0.5-1.0e-20,0.95,0.5-1.0e-20,0.95,1.0,HUGE_VAL};
        int ifault=0;

        // Now minimise lse() function
        // First step is to identify the region of the parameter space with the global min.

        nlopt_opt directOpt=nlopt_create(NLOPT_GN_DIRECT_NOSCAL,6);
        nlopt_set_min_objective(directOpt, lse, (void *) &sp);
        nlopt_set_lower_bounds(directOpt, lb);
        // DIRECT algorithm requires a bounded parameter space
        // So we need to restrict an upper bound of the variance.
        // to do this we use the variance of teh series as a whole as an upper bound.
        ub[5]=ss->processVar();
        nlopt_set_upper_bounds(directOpt, ub);
        // DIRECT algorithm does not handle general inequality constraints.
        //nlopt_add_inequality_constraint(directOpt, bnp_u_seq_constraint, NULL, TOL);

        // Standard termination criteria
        nlopt_set_ftol_abs(directOpt, TOL);
        nlopt_set_maxtime(directOpt, MAXTIME);
        nlopt_set_maxeval(directOpt, MAXEVAL);
        // Now we optimise to get initial values
        optResult=nlopt_optimize(directOpt, x, &lse_val);
        nlopt_destroy(directOpt);

        // Now we see if we need to swap the params around if they are in the wrong order
        if (x[3]<x[1]) {// yes we need to swap them
            double temp0=x[0], temp1=x[1];
            x[0]=x[2]; x[1]=x[3];
            x[2]=temp0; x[3]=temp1;
        };

        // Now we get better accuracy by using a local optimisation method.
        nlopt_opt cobyLAOpt=nlopt_create(NLOPT_LN_COBYLA,6);
        nlopt_set_min_objective(cobyLAOpt, lse, (void *) &sp);
        nlopt_set_lower_bounds(cobyLAOpt, lb);
        // reset the upper bound of the variance
        ub[5]=HUGE_VAL;
        nlopt_set_upper_bounds(cobyLAOpt, ub);
        nlopt_add_inequality_constraint(cobyLAOpt, bnp_u_seq_constraint, NULL, TOL);
        // Standard termination criteria
        nlopt_set_ftol_abs(cobyLAOpt, TOL);
        nlopt_set_maxtime(cobyLAOpt, MAXTIME);
        nlopt_set_maxeval(cobyLAOpt, MAXEVAL);

        optResult=nlopt_optimize(cobyLAOpt, x, &lse_val_c);
        nlopt_destroy(cobyLAOpt);

        calc_d1=x[0];
        calc_u1=x[1];
        calc_d2=x[2];
        calc_u2=x[3];
        calc_phi=x[4];
        calc_sigma2=x[5];
        calc_min_lse=lse_val_c;

        // Correction for bias in sigma2 estimate
        calc_sigma2 = calc_sigma2*exp(-digamma((double) m,&ifault));

        steady_clock::time_point endTime = steady_clock::now();
        duration<double> time_span = duration_cast<duration<double>>(endTime - startTime);
        timeTaken=(double)time_span.count();

        return(optResult);
    };

public:
    double *y;
    nlopt_result optResult, optResult2;

    cBNPEst(int init_n, double *py, int smoothing) {
        y=py;
        m=smoothing;
        if ((m<=0)|(m>(init_n/2))) m=1;
        ss = new cSeriesStats(init_n, py, m);
        n=init_n;
        sp.n=(m>1 ? (ss->kn):init_n);
        sp.m=smoothing;
        sp.y=py;
        sp.cos_2_pi_f=(m>1 ? (ss->cos_2_pi_fk):(ss->cos_2_pi_f));
        sp.logSpec=(m>1 ? ss->logAggSpec:ss->logSpec);
        sp.n_calls=0;
        optResult=findMinLSE();
    };
    ~cBNPEst() {
        ss->~cSeriesStats();
    };
    double Optimal_d1() {return(calc_d1);};
    double Optimal_u1() {return(calc_u1);};
    double Optimal_d2() {return(calc_d2);};
    double Optimal_u2() {return(calc_u2);};
    double Optimal_phi() {return(calc_phi);};
    double Optimal_sigma2() {return(calc_sigma2);};
};

class cRes {
// This class stores the parameter estimates.
// We instantiate this multiple times to store the results from each of the various methods.
private:
    unsigned int maxTrials, nTrials;
    nlopt_result *optRes;
    double *d1_Res, *u1_Res, *d2_Res, *u2_Res, *phi_Res, *sigma2_Res, *timeRes;
    bool *Err;
    double true_d1, true_u1, true_d2, true_u2, true_phi, true_sigma2;
    string name;

public:
    cRes() {
        d1_Res=NULL;
        u1_Res=NULL;
        d2_Res=NULL;
        u2_Res=NULL;
        phi_Res=NULL;
        sigma2_Res=NULL;
        timeRes=NULL;
        optRes=NULL;
        Err=NULL;
    }; // default constructor
    ~cRes() {
        if (optRes!=NULL) free(optRes);
        if (d1_Res!=NULL) free(d1_Res);
        if (u1_Res!=NULL) free(u1_Res);
        if (d2_Res!=NULL) free(d2_Res);
        if (u2_Res!=NULL) free(u2_Res);
        if (phi_Res!=NULL) free(phi_Res);
        if (sigma2_Res!=NULL) free(sigma2_Res);
        if (timeRes!=NULL) free(timeRes);
        if (Err!=NULL) free(Err);
    };
    void Init(unsigned int init_maxTrials, string init_name, double init_d1, double init_u1,
                double init_d2, double init_u2, double init_phi, double init_sigma2) {
        maxTrials=init_maxTrials;
        name=init_name;
        true_d1=init_d1;
        true_u1=init_u1;
        true_d2=init_d2;
        true_u2=init_u2;
        true_phi=init_phi;
        true_sigma2=init_sigma2;
        nTrials=0;
        optRes=(nlopt_result *)malloc(sizeof(nlopt_result)*maxTrials);
        d1_Res=(double *)malloc(sizeof(double)*maxTrials);
        u1_Res=(double *)malloc(sizeof(double)*maxTrials);
        d2_Res=(double *)malloc(sizeof(double)*maxTrials);
        u2_Res=(double *)malloc(sizeof(double)*maxTrials);
        phi_Res=(double *)malloc(sizeof(double)*maxTrials);
        sigma2_Res=(double *)malloc(sizeof(double)*maxTrials);
        timeRes=(double *)malloc(sizeof(double)*maxTrials);
        Err=(bool *)malloc(sizeof(bool)*maxTrials);
        for (unsigned int i=0;i<maxTrials;i++) {
            optRes[i]= (nlopt_result)0;
            d1_Res[i]=0.0;
            u1_Res[i]=0.0;
            d2_Res[i]=0.0;
            u2_Res[i]=0.0;
            phi_Res[i]=0.0;
            sigma2_Res[i]=0.0;
            timeRes[i]=0.0;
            Err[i]=false;
            };
    };
    string result() {
        string txt;
        char cRes1[4096];


        sprintf(cRes1, "%0.2f,%0.2f,%s,Bias,%0.4f,%0.4f,%0.4f,%0.4f,%0.4f,%0.4f,%0.4f\n,,,RMSE,%0.4f,%0.4f,%0.4f,%0.4f,%0.4f,%0.4f\n",
            true_d1, true_d2, name.data(),
            true_d1-d1_Mean(), true_u1-u1_Mean(), true_d2-d2_Mean(), true_u2-u2_Mean(),
            true_phi-phi_Mean(),
            true_sigma2-sigma2_Mean(), meanTime(),
            d1_RMSE(), u1_RMSE(), d2_RMSE(), u2_RMSE(), phi_RMSE(), sigma2_RMSE());
        txt=cRes1;
        return(txt);
        };
    double d1_Mean() {
        double tot=0.0;
        int n=0;
        for (unsigned int i=0;i<nTrials;i++) if(!Err[i]) {tot+=d1_Res[i]; n++;}
        return (tot/((double) n));
    };
    double u1_Mean() {
        double tot=0.0;
        int n=0;
        for (unsigned int i=0;i<nTrials;i++) if(!Err[i]) {tot+=u1_Res[i]; n++;}
        return (tot/((double) n));
    };
    double phi_Mean() {
        double tot=0.0;
        int n=0;
        for (unsigned int i=0;i<nTrials;i++) if(!Err[i]) {tot+=phi_Res[i]; n++;}
        return (tot/((double) n));
    };
    double sigma2_Mean() {
        double tot=0.0;
        int n=0;
        for (unsigned int i=0;i<nTrials;i++) if(!Err[i]) {tot+=sigma2_Res[i]; n++;}
        return (tot/((double) n));
    };
    double d1_RMSE() {
        double tot=0.0;
        int n=0;
        for (unsigned int i=0;i<nTrials;i++)
            if(!Err[i]) {
                tot+= (d1_Res[i]-true_d1)*(d1_Res[i]-true_d1);
                n++;
                };
        return (sqrt(tot/((double) n)));
    };
    double u1_RMSE() {
        double tot=0.0;
        int n=0;
        for (unsigned int i=0;i<nTrials;i++)
            if(!Err[i]) {
                tot+= (u1_Res[i]-true_u1)*(u1_Res[i]-true_u1);
                n++;
                };
        return (sqrt(tot/((double) n)));
    };
    double phi_RMSE() {
        double tot=0.0;
        int n=0;
        for (unsigned int i=0;i<nTrials;i++)
            if(!Err[i]) {
                tot+= (phi_Res[i]-true_phi)*(phi_Res[i]-true_phi);
                n++;
                };
        return (sqrt(tot/((double) n)));
    };
    double d2_Mean() {
        double tot=0.0;
        int n=0;
        for (unsigned int i=0;i<nTrials;i++) if(!Err[i]) {tot+=d2_Res[i]; n++;}
        return (tot/((double) n));
    };
    double u2_Mean() {
        double tot=0.0;
        int n=0;
        for (unsigned int i=0;i<nTrials;i++) if(!Err[i]) {tot+=u2_Res[i]; n++;}
        return (tot/((double) n));
    };
    double d2_RMSE() {
        double tot=0.0;
        int n=0;
        for (unsigned int i=0;i<nTrials;i++)
            if(!Err[i]) {
                tot+= (d2_Res[i]-true_d2)*(d2_Res[i]-true_d2);
                n++;
                };
        return (sqrt(tot/((double) n)));
    };
    double u2_RMSE() {
        double tot=0.0;
        int n=0;
        for (unsigned int i=0;i<nTrials;i++)
            if(!Err[i]) {
                tot+= (u2_Res[i]-true_u2)*(u2_Res[i]-true_u2);
                n++;
                };
        return (sqrt(tot/((double) n)));
    };
    double sigma2_RMSE() {
        double tot=0.0;
        int n=0;
        for (unsigned int i=0;i<nTrials;i++)
            if(!Err[i]) {
                tot+= (sigma2_Res[i]-true_sigma2)*(sigma2_Res[i]-true_sigma2);
                n++;
                };
        return (sqrt(tot/((double) n)));
    };
    double totalTime() {
        double tot=0.0;
        for (unsigned int i=0;i<nTrials;i++) tot+=timeRes[i];
        return (tot);
    };
    double meanTime() {return(totalTime()/((double) nTrials));};
    int Err_Count() {
        int n=0;
        for (unsigned int i=0;i<nTrials;i++) if (Err[i]) n++;
        return(n);
    };
    void addNewResult() {
        optRes[nTrials]=(nlopt_result)0;
        d1_Res[nTrials]=0.0;
        u1_Res[nTrials]=0.0;
        d2_Res[nTrials]=0.0;
        u2_Res[nTrials]=0.0;
        phi_Res[nTrials]=0.0;
        sigma2_Res[nTrials]=0.0;
        timeRes[nTrials]=0.0;
        Err[nTrials]=false;
        nTrials++;
        };
    void addResult(double d1, double u1, double d2, double u2, double phi, double sigma2, nlopt_result opt,double timeTkn) {
        optRes[nTrials-1]=opt;
        d1_Res[nTrials-1]=d1;
        u1_Res[nTrials-1]=u1;
        d2_Res[nTrials-1]=d2;
        u2_Res[nTrials-1]=u2;
        phi_Res[nTrials-1]=phi;
        sigma2_Res[nTrials-1]=sigma2;
        timeRes[nTrials-1]=timeTkn;
    };
    void addErr() {Err[nTrials-1]=true;};
};

class cMonteCarloTrials {
// This class runs the trials, for a given set of "true" parameter estimates.
private:
    unsigned int nTrials, dist;
    double true_d1;
    double true_u1;
    double true_d2;
    double true_u2;
    double true_phi;
    double true_sigma2;
public:
    cRes BNPRes, BNPRes2, BNPRes3, CSSRes, WhittleRes;
    cMonteCarloTrials(unsigned int init_nTrials, double init_d1, double init_u1, double init_d2, double init_u2,
                        double init_phi, double init_sigma2, unsigned int init_dist) {
        nTrials=init_nTrials;
        true_d1=init_d1;
        true_u1=init_u1;
        true_d2=init_d2;
        true_u2=init_u2;
        true_phi=init_phi;
        true_sigma2=init_sigma2;

        dist=init_dist;
        BNPRes.Init(nTrials,"BNP",true_d1,true_u1,true_d2,true_u2,true_phi,true_sigma2);
        BNPRes2.Init(nTrials,"BNP2",true_d1,true_u1,true_d2,true_u2,true_phi,true_sigma2);
        BNPRes3.Init(nTrials,"BNP3",true_d1,true_u1,true_d2,true_u2,true_phi,true_sigma2);
        CSSRes.Init(nTrials,"CSS",true_d1,true_u1,true_d2,true_u2,true_phi,true_sigma2);
        WhittleRes.Init(nTrials,"Whittle",true_d1,true_u1,true_d2,true_u2,true_phi,true_sigma2);
    };
    string Summary() {
        string txt;

        txt=BNPRes.result()
            + BNPRes2.result()
            + BNPRes3.result()
            + CSSRes.result()
            + WhittleRes.result()
            ;
        return(txt);
    };
    void runTrials() {
        // Set up our Simulation object;
        cSimulate cs(ser_len, true_d1, true_u1, true_d2, true_u2, true_phi, true_sigma2, dist);

        for (unsigned int trial=0;trial<nTrials;trial++) {
            cs.GenerateProcess();

            BNPRes.addNewResult();
            BNPRes2.addNewResult();
            BNPRes3.addNewResult();
            CSSRes.addNewResult();
            WhittleRes.addNewResult();


            cBNPEst BNPEst(ser_len, cs.y, 1);
            if ((BNPEst.optResult<0)||(BNPEst.optResult==NLOPT_MAXTIME_REACHED)) BNPRes.addErr();
            else BNPRes.addResult(BNPEst.Optimal_d1(),BNPEst.Optimal_u1(),BNPEst.Optimal_d2(),BNPEst.Optimal_u2(),BNPEst.Optimal_phi(),BNPEst.Optimal_sigma2(),BNPEst.optResult,BNPEst.timeTaken);

            cBNPEst BNPEst2(ser_len, cs.y, 2);
            if ((BNPEst2.optResult<0)||(BNPEst2.optResult==NLOPT_MAXTIME_REACHED)) BNPRes2.addErr();
            else BNPRes2.addResult(BNPEst2.Optimal_d1(),BNPEst2.Optimal_u1(),BNPEst2.Optimal_d2(),BNPEst2.Optimal_u2(),BNPEst2.Optimal_phi(),BNPEst2.Optimal_sigma2(),BNPEst2.optResult,BNPEst2.timeTaken);

            cBNPEst BNPEst3(ser_len, cs.y, 3);
            if ((BNPEst3.optResult<0)||(BNPEst3.optResult==NLOPT_MAXTIME_REACHED)) BNPRes3.addErr();
            else BNPRes3.addResult(BNPEst3.Optimal_d1(),BNPEst3.Optimal_u1(),BNPEst3.Optimal_d2(),BNPEst3.Optimal_u2(),BNPEst3.Optimal_phi(),BNPEst3.Optimal_sigma2(),BNPEst3.optResult,BNPEst3.timeTaken);

            cCSSEst CSSEst(ser_len, cs.y);
            if ((CSSEst.optResult<0)||(CSSEst.optResult==NLOPT_MAXTIME_REACHED)) CSSRes.addErr();
            else CSSRes.addResult(CSSEst.Optimal_d1(), CSSEst.Optimal_u1(), CSSEst.Optimal_d2(), CSSEst.Optimal_u2(), CSSEst.Optimal_phi(), CSSEst.Optimal_sigma2(),CSSEst.optResult,CSSEst.timeTaken);

            cWHTLEst WHTLEst(ser_len, cs.y,1);
            if ((WHTLEst.optResult<0)||(WHTLEst.optResult==NLOPT_MAXTIME_REACHED)) WhittleRes.addErr();
            else
                WhittleRes.addResult(WHTLEst.Optimal_d1(), WHTLEst.Optimal_u1(), WHTLEst.Optimal_d2(), WHTLEst.Optimal_u2(), WHTLEst.Optimal_phi(), WHTLEst.Optimal_sigma2(),WHTLEst.optResult,WHTLEst.timeTaken);

       };
    };
};


int main(int argc, char* argv[])
{
    string infoStr="Gegenbauer Series Simulations.\narg[1] = Series length\narg[2] = Series Variance\narg[3] = 1st (cosine of) Gegenbauer Frequency (u)\narg[4] = 2nd (cosine of) Gegenbauer Frequency (u)\narg[5] = Series distribution - one of gauss, chisq, student, tdist, tdist2\n\n";

    unsigned int dist=0;
    double d1,u1,d2,u2,sigma2=1.0;

    if (argc<=1) {
        cout << infoStr;
        return(0);
        };

    if (argc>1) {
        if ((strcmp(argv[1],"-h")==0)||(strcmp(argv[1],"-help")==0)||(strcmp(argv[1],"-?")==0)) {
            cout << infoStr;
            return(0);
            }
        };

    if (argc>1) {
        int n;
        sscanf(argv[1], "%d", &n);
        if ((n<50)||(n>SER_LEN)) {
            cerr << "Invalid Series Length: " << argv[1] <<endl << "Series Length set to " << SER_LEN << endl;
            ser_len=SER_LEN;
            }
        else ser_len=n;
        };

    if (argc>2) {// sigma2
        double sig2;
        sscanf(argv[2], "%lf", &sig2);
        if (sig2<=0.0) {
            cerr << "Invalid variance: " << argv[2] <<endl << "Series variance set to 1.0" << endl;
            sigma2=1.0;
            }
        else sigma2=sig2;
        };

    if (argc>3) {// u1
        sscanf(argv[3], "%lf", &u1);
        if ((u1<=-1.0)||(u1>=1.0)) {
            cerr << "Invalid 1st Gegenbauer Frequency: " << argv[3] <<endl << "Gegenbauer Frequency set to 0.2" << endl;
            u1=0.2;
            }
        };
    if (argc>4) {// u2
        sscanf(argv[4], "%lf", &u2);
        if ((u2<=-1.0)||(u2>=1.0)) {
            cerr << "Invalid 2nd Gegenbauer Frequency: " << argv[4] <<endl << "Gegenbauer Frequency set to 0.2" << endl;
            u2=0.8;
            }
        };

    if (argc>5) {
        if (strcmp(argv[5],"gauss")==0)
            dist=0;
        if (strcmp(argv[5],"chisq")==0)
            dist=2;
        if (strcmp(argv[5],"student")==0)
            dist=1;
        if (strcmp(argv[5],"tdist")==0)
            dist=1;
        if (strcmp(argv[5],"tdist2")==0)
            dist=3;
        if (strcmp(argv[5],"t-dist")==0)
            dist=1;
        if (strcmp(argv[5],"sq-gauss")==0)
            dist=4;
        if (strcmp(argv[5],"chisq3")==0)
            dist=5;
        if (strcmp(argv[5],"vg")==0)
            dist=6;
        if (strcmp(argv[5],"gamma")==0)
            dist=7;
        if (strcmp(argv[5],"laplace")==0)
            dist=8;
        if (strcmp(argv[5],"tdist3")==0)
            dist=9;
        if (strcmp(argv[5],"change")==0)
            dist=10;
        if (strcmp(argv[5],"gamma3")==0)
            dist=11;
        };
    cout << "Running " << MAX_TRIALS << " trials of length " << ser_len << " from ";
    if (dist==0)
        cout << "Gaussian";
    if (dist==1)
        cout << "Student t-dist(df=5)";
    if (dist==2)
        cout << "Chi-Sq(df=1)";
    if (dist==3)
        cout << "Student t-dist(df=2)";
    if (dist==4)
        cout << "Gaussian-Squared";
    if (dist==5)
        cout << "Chi-Sq(df=3)";
    if (dist==6)
        cout << "Variance-Gamma(" << VG_THETA << "," << VG_NU << "," << VG_SIGMA2 << ")";
    if (dist==7)
        cout << "Gamma(0.25,2.0)";
    if (dist==8)
        cout << "Laplace";
    if (dist==9)
        cout << "Student t-dist(df=6)";
    if (dist==10)
        cout << "Gamma Changing";
    if (dist==11)
        cout << "Gamma(3,2)";
    cout << " distribution." << endl << endl;

    cout << "d1,d2,Method,,d1,u1,d2,u2,phi,s2,Avg Time\n";
    for (d1=0.15;d1<0.46;d1+=0.15)
        for (d2=0.15;d2<0.46;d2+=0.15)
                {
                    cMonteCarloTrials mct(MAX_TRIALS, d1, u1, d2, u2, 0.8, sigma2, dist);
                    mct.runTrials();
                    cout << mct.Summary();
                    cout.flush();
                    };
    return 0;
}
