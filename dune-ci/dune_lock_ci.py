#!/usr/bin/env python3
"""Script to lock dune dune build jobs
 during dune cache cleanup"""

import sys
import argparse
import requests
from retry import retry


class RetryStatusError(Exception):
    """Handle job status exceptions"""


DEBUG = 1

# Update below dictionary with all repos/CI-jobs with dune proof builds
repodata = {
    "bhv": {
        "id": "16203504",
        "dune_job": "proof-dune-bhv",
        "cleanup_job": "dune-cache-cleanup"
    },
    "cpp2v": {
        "id": "18556810",
        "dune_job": "dune-build"
    },
    "cpp2v-core": {
        "id": "12945770",
        "dune_job": "dune-build"
    }
}


def parse_cmd(argv):
    """Parse command line arguments."""
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(help='commands', dest='command')

    # list  parser
    trim_parser = subparsers.add_parser('check_dune_build_job',
                                        help='Check status for dune proof \
                                            jobs before trimming cache')
    trim_parser.add_argument('-t', '--citoken', help='gitlab token',
                             action='store', required=True, dest='citoken')
    proof_parser = subparsers.add_parser('check_cleanup_job',
                                         help='check status for dune cache \
                                            trim job')
    proof_parser.add_argument('-t', '--citoken', help='gitlab token',
                              action='store', required=True, dest='citoken')
    if not any(arg_p in ['check_dune_build_job', 'check_cleanup_job', '--help',
               '-h'] for arg_p in argv[1:]):
        parser.parse_args(['-h'])
    return parser.parse_args(argv[1:])


def get_project_url(project, job_type):
    """get project url"""
    project_url = ''
    url_prefix = 'https://gitlab.com/api/v4/projects/'
    if job_type == "dune_job":
        url_suffix = f'{repodata[project]["id"]}/jobs' + \
            f'?job={repodata[project][job_type]}'
    elif job_type == "cleanup_job":
        url_suffix = f'{repodata[project]["id"]}/pipelines' + \
            '?source=schedule&per_page=8'
    else:
        url_suffix = f'{repodata[project]["id"]}/pipelines/' + \
            f'{job_type}/jobs?job={repodata[project]["cleanup_job"]}'
    project_url = url_prefix + url_suffix
    return project_url


@retry(ConnectionError, delay=10, tries=10)
def api_get_request(url, ci_token):
    """api request to gitlab"""
    session = requests.Session()
    mytoken = ci_token
    head = {'PRIVATE-TOKEN': mytoken}
    if DEBUG:
        print("api_get_request", url)
    response = session.get(url,
                           headers=head)
    if not response:
        print("No response")
        raise ConnectionError("Connection Error")
    if response.status_code != 200:
        raise ConnectionError("Connection Error")
    return response


@retry(RetryStatusError, delay=180, tries=10)
def get_project_job_status(project, url, citoken, dune_job):
    """fetch specified job status"""
    clr_warn = '\033[93m'
    clr_reset = '\033[0m'
    run_status = ["running", "created", "pending", "scheduled"]
    rp_data = api_get_request(url, citoken)
    if rp_data:
        for item in rp_data.json():
            if item['name'] == dune_job:
                if DEBUG == 1:
                    print(item['name'], item['status'])
                if item['status'] in run_status:
                    print(f"{clr_warn}Dune build Job \"{dune_job}\" is " +
                          f"{item['status']} in {project}")
                    print(f"Retrying after 180 seconds{clr_reset}")
                    raise RetryStatusError
                return item['status']
    return None


def get_dune_build_job_status(citoken):
    """get dune job project status"""
    job_type = "dune_job"
    for project in repodata:  # pylint: disable=C0206
        url = get_project_url(project, job_type)
        dune_job = repodata[project][job_type]
        if DEBUG == 1:
            print(project)
        status = get_project_job_status(project, url, citoken, dune_job)
        print(f'{project} status: {status}')


def get_status_from_pipeline(project, pipe_id, citoken):
    """fetch schedule pipelines data"""
    url = get_project_url(project, pipe_id)
    rp_data = api_get_request(url, citoken)
    if rp_data:
        for item in rp_data.json():
            if item['name'] == repodata[project]['cleanup_job']:
                return item['status']
    return None


def get_dune_cleanup_status(citoken):
    """get dune cache cleanup job status"""
    clr_warn = '\033[91m'
    clr_reset = '\033[0m'
    project = "bhv"
    job_type = "cleanup_job"
    run_status = ["running", "created", "pending", "scheduled"]
    url = get_project_url(project, job_type)
    dune_job = repodata[project][job_type]
    rp_data = api_get_request(url, citoken)
    if rp_data:
        for item in rp_data.json():
            cache_job_status = get_status_from_pipeline(project, item['id'], citoken)
            if cache_job_status:
                print(dune_job, cache_job_status)
                if cache_job_status in run_status:
                    print(f"{clr_warn}Dune Cleanup job \"{dune_job}\" is " +
                          f"{item['status']} in {project}")
                    print("Re-run CI after cache cleanup is completed")
                    print(f"Exiting ...{clr_reset}")
                    sys.exit(-1)
                sys.exit()
            else:
                print("Unable to fetch cache job data")


if __name__ == "__main__":
    args = parse_cmd(sys.argv)
    if args.command == "check_dune_build_job":
        get_dune_build_job_status(args.citoken)
    elif args.command == "check_cleanup_job":
        get_dune_cleanup_status(args.citoken)
    sys.exit(0)
