# Name: AGM-Robotics
poly_list:=map(numer,
[z_1^2*z_2^2+2/q_2*z_1^2*z_2+2/q_2*(1-b)*z_1*z_2^2+z_1^2+z_2^2-2/q_2*(1+b)*z_1-2/q_2*z_2+1, (1-b-q_1)*z_1^2*z_2^2-(1+b+q_1)*z_1^2-4*z_1*z_2-(1-b+q_1)*z_2^2+1+b-q_1]):
parm_list:=[q_1, q_2, b]:
var_list:=[z_1, z_2]:
